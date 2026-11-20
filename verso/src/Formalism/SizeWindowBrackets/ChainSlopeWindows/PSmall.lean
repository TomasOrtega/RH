import Formalism.SizeWindowBrackets.SSmall
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LSmall

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (translation)
Introduce `m TT T2 x b b' η κ w'' off bt w ⟨hb, hb', hη, hκ, hx, hoff0, hoff, hw0, hw'', hbt, hsum⟩ ⟨hthick, htop, hthin⟩`. Establish `hκb : 0 ≤ κ * b'` using `by positivity`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u0 j ρ hρ`. Distinguish the cases in `h1 : IsThickAt T2 u0 ρ`.

Combine the linear relations using `[(hthick u0 j ρ h1).1]`. Distinguish the cases in `h2 : ∀ t ∈ TT, ρ ≠ topPl t`. Combine the linear relations using `[(hthin u0 j ρ hρ h1 h2).1]`. Use `push Not at h2`. Take `⟨t, ht, rfl⟩` from `h2`.

Combine the linear relations using `[(htop u0 j t ht).1, (hbt t ht).1]`. Introduce `u0 j ρ h1`. Use `hthick u0 j ρ h1` as an intermediate fact. Conclude with `⟨this.1, by linarith [this.2]⟩`. Introduce `u0 j ρ hρ h1`.

Distinguish the cases in `h2 : ∀ t ∈ TT, ρ ≠ topPl t`. Combine the linear relations using `[(hthin u0 j ρ hρ h1 h2).2]`. Use `push Not at h2`. Take `⟨t, ht, rfl⟩` from `h2`. Combine the linear relations using `[(htop u0 j t ht).2, (hbt t ht).2]`.
-/
theorem node_sizes_of_windows : NodeSizesOfWindows (H := H) := by
  intro m TT T2 x b b' η κ w'' off bt w ⟨hb, hb', hη, hκ, hx, hoff0, hoff, hw0, hw'', hbt, hsum⟩ ⟨hthick, htop, hthin⟩
  have hκb : 0 ≤ κ * b' := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro u0 j ρ hρ
    by_cases h1 : IsThickAt T2 u0 ρ
    · linarith [(hthick u0 j ρ h1).1]
    by_cases h2 : ∀ t ∈ TT, ρ ≠ topPl t
    · linarith [(hthin u0 j ρ hρ h1 h2).1]
    push Not at h2
    obtain ⟨t, ht, rfl⟩ := h2
    linarith [(htop u0 j t ht).1, (hbt t ht).1]
  · intro u0 j ρ h1
    have := hthick u0 j ρ h1
    exact ⟨this.1, by linarith [this.2]⟩
  · intro u0 j ρ hρ h1
    by_cases h2 : ∀ t ∈ TT, ρ ≠ topPl t
    · linarith [(hthin u0 j ρ hρ h1 h2).2]
    push Not at h2
    obtain ⟨t, ht, rfl⟩ := h2
    linarith [(htop u0 j t ht).2, (hbt t ht).2]

end

/- English proof (translation)
Introduce `H _ _ _ TT x b b' η κ off bt hx hb hb' hη hη4 hκ hκ4 hoff hbt`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hn : (1 : ℝ) ≤ (Fintype.card H : ℝ)` using `by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H)`. Establish `hq0 : 0 ≤ b' / x` using `by positivity`. Establish `hq3 : b' / x ≤ b' / 3` using `div_le_div_of_nonneg_left hb'.le (by norm_num) hx`.

Use `⟨hb, hb', hη, hκ, hx0, ?_, ?_, by positivity, ?_, hbt, ?_⟩` and prove the remaining obligations. Break down `hoff with rfl | rfl` into its components or cases. Conclude with `hq0`. Conclude with `Int.floor_nonneg.2 hq0` after adjusting the coercions. Break down `hoff with rfl | rfl` into its components or cases.

Conclude with `le_refl _`. Conclude with `Int.floor_le _`. Apply `div_le_div_of_nonneg_left hb'.le hx0` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `: κ * b' ≤ 1 / 4 * b'` using `mul_le_mul_of_nonneg_right hκ4 hb'.le`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem window_sizes_explicit : WindowSizesText := by
  intro H _ _ _ TT x b b' η κ off bt hx hb hb' hη hη4 hκ hκ4 hoff hbt
  have hx0 : 0 < x := by linarith
  have hn : (1 : ℝ) ≤ (Fintype.card H : ℝ) := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H)
  have hq0 : 0 ≤ b' / x := by positivity
  have hq3 : b' / x ≤ b' / 3 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
  refine ⟨hb, hb', hη, hκ, hx0, ?_, ?_, by positivity, ?_, hbt, ?_⟩
  · rcases hoff with rfl | rfl
    · exact hq0
    · exact_mod_cast Int.floor_nonneg.2 hq0
  · rcases hoff with rfl | rfl
    · exact le_refl _
    · exact Int.floor_le _
  · apply div_le_div_of_nonneg_left hb'.le hx0
    nlinarith
  · have : κ * b' ≤ 1 / 4 * b' := mul_le_mul_of_nonneg_right hκ4 hb'.le
    linarith

/- English proof (translation)
Introduce `H _ _ _ m TT T2 x b b' η κ off bt w h1 h2 h3 h4 h5 h6 h7 h8 h9 hw`. Conclude with `node_sizes_of_windows TT T2 x b b' η κ _ off bt w (window_sizes_explicit H TT x b b' η κ off bt h1 h2 h3 h4 h5 h6 h7 h8 h9) hw`.
-/
theorem node_sizes_explicit : NodeSizesText := by
  intro H _ _ _ m TT T2 x b b' η κ off bt w h1 h2 h3 h4 h5 h6 h7 h8 h9 hw
  exact node_sizes_of_windows TT T2 x b b' η κ _ off bt w
    (window_sizes_explicit H TT x b b' η κ off bt h1 h2 h3 h4 h5 h6 h7 h8 h9) hw

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

end

section Conj

open Matrix Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma cj_apply {m n : Type} (M : Matrix m n ℂ) (i : m) (j : n) : cj M i j = starRingEnd ℂ (M i j) := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cj_apply]`.
-/
lemma cj_cj {m n : Type} (M : Matrix m n ℂ) : cj (cj M) = M := by
  ext i j; simp [cj_apply]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cj_apply]`.
-/
lemma cj_sub {m n : Type} (M N : Matrix m n ℂ) : cj (M - N) = cj M - cj N := by
  ext i j; simp [cj_apply]

section
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}

end

end Conj

section Host

open Formalism.LFunctionChainParameters.LHost
open Formalism.FrobeniusOrbits (HostHyp HGrp hcl)

/- English proof (translation)
The claim follows from `dif_pos h`.
-/
lemma hOf_of_coprime {e m : ℕ} (h : m.Coprime (2 ^ (e + 2))) :
    hOf e m = Additive.ofMul (hcl e (ZMod.unitOfCoprime m h)) := dif_pos h

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

end

/- English proof (translation)
Introduce `h`. Use `congrArg (fun x : E0 × H => x.1.2) h` as an intermediate fact. Simplify using `[sg] at this`.
-/
lemma sg_ne {H : Type} [AddCommGroup H] : (0 : E0 × H) ≠ sg := by
  intro h
  have := congrArg (fun x : E0 × H => x.1.2) h
  simp [sg] at this

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

end

/- English proof (translation)
Rewrite using `[Nat.coprime_pow_right_iff (by omega), Nat.coprime_two_right]`.
-/
lemma odd_iff_cop (e m : ℕ) : Odd m ↔ m.Coprime (2 ^ (e + 2)) := by
  rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_two_right]

/- English proof (translation)
Rewrite using `[hOf_of_coprime (Nat.coprime_one_left _), unitOfCoprime_one]`. Both sides reduce to the same expression.
-/
lemma hOf_one (e : ℕ) : hOf e 1 = 0 := by
  rw [hOf_of_coprime (Nat.coprime_one_left _), unitOfCoprime_one]
  rfl

/- English proof (translation)
Establish `ca` using `(odd_iff_cop e a).1 ha`. Establish `cb` using `(odd_iff_cop e b).1 hb`. Rewrite using `[hOf_of_coprime ca, hOf_of_coprime cb, hOf_of_coprime (Nat.Coprime.mul_left ca cb)]`. Establish `: ZMod.unitOfCoprime (a * b) (Nat.Coprime.mul_left ca cb) = ZMod.unitOfCoprime a ca * ZMod.unitOfCoprime b cb` using `by ext; simp`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
lemma hOf_mul (e : ℕ) {a b : ℕ} (ha : Odd a) (hb : Odd b) : hOf e (a * b) = hOf e a + hOf e b := by
  have ca := (odd_iff_cop e a).1 ha
  have cb := (odd_iff_cop e b).1 hb
  rw [hOf_of_coprime ca, hOf_of_coprime cb, hOf_of_coprime (Nat.Coprime.mul_left ca cb)]
  have : ZMod.unitOfCoprime (a * b) (Nat.Coprime.mul_left ca cb) = ZMod.unitOfCoprime a ca * ZMod.unitOfCoprime b cb := by
    ext; simp
  rw [this]
  rfl

/- English proof (translation)
Unfold `omV`. Use `split_ifs with h1 h2`. Both sides reduce to the same expression. Rewrite using `[hOf_one]`. Conclude with `AddChar.map_zero_eq_one ψ`.

Conclude with `absurd odd_one h2`.
-/
lemma omV_one (e : ℕ) (ψ : AddChar (E0 × HA e) ℂ) : omV e ψ 1 = 1 := by
  unfold omV
  split_ifs with h1 h2
  · rfl
  · rw [hOf_one]; exact AddChar.map_zero_eq_one ψ
  · exact absurd odd_one h2

/- English proof (translation)
Unfold `omV`. Distinguish the cases in `h1 : ∀ t : HA e, ψ ((0, 0), t) = 1`. Simplify using `only [if_pos h1, mul_one]`. Simplify using `only [if_neg h1]`. Distinguish the cases in `ha : Odd a`.

Distinguish the cases in `hb : Odd b`. Rewrite using `[if_pos ha, if_pos hb, if_pos (ha.mul hb), hOf_mul e ha hb, ← AddChar.map_add_eq_mul]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hb, if_neg (fun h => hb (Nat.odd_mul.1 h).2), mul_zero]`. Rewrite using `[if_neg ha, if_neg (fun h => ha (Nat.odd_mul.1 h).1), zero_mul]`.
-/
lemma omV_mul (e : ℕ) (ψ : AddChar (E0 × HA e) ℂ) (a b : ℕ) : omV e ψ (a * b) = omV e ψ a * omV e ψ b := by
  unfold omV
  by_cases h1 : ∀ t : HA e, ψ ((0, 0), t) = 1
  · simp only [if_pos h1, mul_one]
  simp only [if_neg h1]
  by_cases ha : Odd a
  · by_cases hb : Odd b
    · rw [if_pos ha, if_pos hb, if_pos (ha.mul hb), hOf_mul e ha hb, ← AddChar.map_add_eq_mul]
      simp
    · rw [if_neg hb, if_neg (fun h => hb (Nat.odd_mul.1 h).2), mul_zero]
  · rw [if_neg ha, if_neg (fun h => ha (Nat.odd_mul.1 h).1), zero_mul]

/- English proof (translation)
Unfold `laV`. Use `split_ifs`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
lemma laV_one (s : ℂ) (l : ℕ) : laV s l 1 = 1 := by
  unfold laV
  split_ifs
  · rfl
  · simp

/- English proof (translation)
Unfold `laV`. Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[Nat.cast_mul, jacobiSym.mul_left]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
lemma laV_mul (s : ℂ) (l a b : ℕ) : laV s l (a * b) = laV s l a * laV s l b := by
  unfold laV
  split_ifs
  · simp
  · rw [Nat.cast_mul, jacobiSym.mul_left]; push_cast; rfl

def prodHom (e q d : ℕ) (ψ : AddChar (E0 × HA e) ℂ) : ℕ →* ℂ where
  toFun m := omV e ψ m * laV (ψ sg) q m * laV (ψ sgc0) d m
  map_one' := by rw [omV_one, laV_one, laV_one]; norm_num
  map_mul' a b := by rw [omV_mul, laV_mul, laV_mul]; ring

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

end

end Host

end Formalism.LFunctionChainParameters.LSmall
