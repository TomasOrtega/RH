import Formalism.SizeWindowBrackets.SSmall
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LSmall

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (authored)
A thick node has positive weight because its lower bound is b > 0. Any other permitted node either is among the listed top places, where its lower bound is bₜ plus the nonnegative offset and bₜ ≥ b′ > 0, or has lower bound w″ > 0. The thick upper bound is already b + η + 1. At a non-thick top place, the upper bound is at most b′ + κb′ + b′/x + η ≤ 2b′. At any other non-thick place, the upper bound is w″ + η ≤ b′/x + η ≤ b′, which also gives the required bound.
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

/- English proof (authored)
The ratio b′/x is positive and at most b′/3. Either that ratio or its floor is nonnegative and bounded above by the ratio. The group has at least one element, so dividing the ratio by the group order gives a positive thin width no larger than b′/x. The three contributions to the remaining constraint are bounded by b′/4, b′/3 and b′/4. Their sum is at most b′.
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

/- English proof (authored)
The explicit parameter bounds furnish the window-size conditions with thin width b′ divided by x times the group order, with both factors in the denominator. Apply the node-size estimate to these conditions and the assumed local windows.
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

/- English proof (authored)
The conjugated matrix is obtained by applying complex conjugation to each entry. Its entry at row i and column j is therefore the conjugate of the corresponding original entry.
-/
lemma cj_apply {m n : Type} (M : Matrix m n ℂ) (i : m) (j : n) : cj M i j = starRingEnd ℂ (M i j) := rfl

/- English proof (authored)
At each entry, conjugating twice returns the original complex number. Equality of all entries gives the matrix identity.
-/
lemma cj_cj {m n : Type} (M : Matrix m n ℂ) : cj (cj M) = M := by
  ext i j; simp [cj_apply]

/- English proof (authored)
Complex conjugation preserves subtraction. Apply that identity to each entry of the difference to obtain the matrix equality.
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

/- English proof (authored)
Under the coprimality hypothesis, the construction takes the residue of m as a unit and sends it to its quotient class, written in additive notation.
-/
lemma hOf_of_coprime {e m : ℕ} (h : m.Coprime (2 ^ (e + 2))) :
    hOf e m = Additive.ofMul (hcl e (ZMod.unitOfCoprime m h)) := dif_pos h

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

end

/- English proof (authored)
Project the proposed equality to the second coordinate of the first factor. It would identify zero with one in the two-element group, which is impossible.
-/
lemma sg_ne {H : Type} [AddCommGroup H] : (0 : E0 × H) ≠ sg := by
  intro h
  have := congrArg (fun x : E0 × H => x.1.2) h
  simp [sg] at this

section
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]

end

/- English proof (authored)
The exponent e + 2 is positive, so coprimality with 2 to that power is equivalent to coprimality with 2. A natural number is coprime to 2 exactly when it is odd.
-/
lemma odd_iff_cop (e m : ℕ) : Odd m ↔ m.Coprime (2 ^ (e + 2)) := by
  rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_two_right]

/- English proof (authored)
The residue of 1 gives the identity unit. Its quotient class is the multiplicative identity, hence zero in the additive notation.
-/
lemma hOf_one (e : ℕ) : hOf e 1 = 0 := by
  rw [hOf_of_coprime (Nat.coprime_one_left _), unitOfCoprime_one]
  rfl

/- English proof (authored)
Both odd factors and their product are coprime to the modulus. The unit represented by the product is the product of the units represented by the factors, as seen on their underlying residues. Passing to the quotient preserves products, which are written as sums in the additive group.
-/
lemma hOf_mul (e : ℕ) {a b : ℕ} (ha : Odd a) (hb : Odd b) : hOf e (a * b) = hOf e a + hOf e b := by
  have ca := (odd_iff_cop e a).1 ha
  have cb := (odd_iff_cop e b).1 hb
  rw [hOf_of_coprime ca, hOf_of_coprime cb, hOf_of_coprime (Nat.Coprime.mul_left ca cb)]
  have : ZMod.unitOfCoprime (a * b) (Nat.Coprime.mul_left ca cb) = ZMod.unitOfCoprime a ca * ZMod.unitOfCoprime b cb := by
    ext; simp
  rw [this]
  rfl

/- English proof (authored)
When the character is trivial on the quotient factor, the value is one by definition. Otherwise the input 1 is odd, and its quotient class is zero. The additive character takes zero to one.
-/
lemma omV_one (e : ℕ) (ψ : AddChar (E0 × HA e) ℂ) : omV e ψ 1 = 1 := by
  unfold omV
  split_ifs with h1 h2
  · rfl
  · rw [hOf_one]; exact AddChar.map_zero_eq_one ψ
  · exact absurd odd_one h2

/- English proof (authored)
When the character is trivial on the quotient factor, the function is constantly one. Otherwise an even factor causes both the product value and the corresponding factor value to vanish. When both factors are odd, the quotient class of their product is the sum of the classes, and evaluation by the additive character turns that sum into multiplication.
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

/- English proof (authored)
For the trivial parameter the function is constantly one. In the other case its value at 1 is the Jacobi symbol with numerator 1, which equals one.
-/
lemma laV_one (s : ℂ) (l : ℕ) : laV s l 1 = 1 := by
  unfold laV
  split_ifs
  · rfl
  · simp

/- English proof (authored)
In the trivial case the function is constantly one. Otherwise use multiplicativity of the Jacobi symbol in its numerator. Embedding the symbol values into the complex numbers preserves the multiplication.
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
