import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.HighestWeightDifferencesNat
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InnerEqZeroOfWeight

open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight CasK kSpan)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open GlobalTheory.CompanionTheory.KLowSpan (kcomm_apply inner_eq_zero_of_weight kstab_orthogonal)

noncomputable section

namespace GlobalTheory.CompanionTheory.KWeightMajor

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

def shift (μ : Fin n → ℝ) (a b : Fin n) (k : ℕ) : Fin n → ℝ :=
  fun c => μ c + k * ((if c = a then 1 else 0) - (if c = b then 1 else 0))

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `c`. Simplify using `only [pow_zero, Module.End.one_apply, shift, Nat.cast_zero, zero_mul, add_zero]`. Conclude with `hz c`.

Consider the case `succ k ih`. Introduce `c`. Rewrite using `[pow_succ', Module.End.mul_apply, kcomm_apply hF rfl he, ih c, map_smul]`. Apply the tactic sequence `by_cases h1 : c = a <;> by_cases h2 : b = c`. Substitute `h1` using the available equality.

Substitute `h2` using the available equality. Simplify using `[shift]`. Substitute `h1` using the available equality. Establish `h2' : ¬ c = b` using `fun h => h2 h.symm`. Simplify using `only [shift, if_pos rfl, if_neg h2', if_neg h2, sub_zero, mul_one]`.

Use `push_cast`. Simplify using `only [mul_one, add_smul, one_smul]`. Normalize the expressions using the abelian group laws. Substitute `h2` using the available equality. Establish `h1' : ¬ b = a` using `h1`.

Simplify using `only [shift, if_pos rfl, if_neg h1', zero_sub, mul_neg, mul_one, zero_sub]`. Use `push_cast`. Simplify using `only [sub_eq_add_neg, mul_one, add_smul, neg_add, neg_smul, one_smul]`. Normalize the expressions using the abelian group laws. Establish `h2' : ¬ c = b` using `fun h => h2 h.symm`.

Simplify using `only [shift, if_neg h1, if_neg h2', if_neg h2, sub_zero, mul_zero, add_zero]`.
-/
lemma isWeight_pow (hF : KRel ε E) {a b : Fin n} (he : ε a = ε b) {μ : Fin n → ℝ} {z : V}
    (hz : IsWeight E μ z) (k : ℕ) : IsWeight E (shift μ a b k) ((E a b ^ k) z) := by
  induction k with
  | zero =>
    intro c
    simp only [pow_zero, Module.End.one_apply, shift, Nat.cast_zero, zero_mul, add_zero]
    exact hz c
  | succ k ih =>
    intro c
    rw [pow_succ', Module.End.mul_apply, kcomm_apply hF rfl he, ih c, map_smul]
    by_cases h1 : c = a <;> by_cases h2 : b = c
    · subst h1; subst h2
      simp [shift]
    · subst h1
      have h2' : ¬ c = b := fun h => h2 h.symm
      simp only [shift, if_pos rfl, if_neg h2', if_neg h2, sub_zero, mul_one]
      push_cast
      simp only [mul_one, add_smul, one_smul]
      abel
    · subst h2
      have h1' : ¬ b = a := h1
      simp only [shift, if_pos rfl, if_neg h1', zero_sub, mul_neg, mul_one, zero_sub]
      push_cast
      simp only [sub_eq_add_neg, mul_one, add_smul, neg_add, neg_smul, one_smul]
      abel
    · have h2' : ¬ c = b := fun h => h2 h.symm
      simp only [shift, if_neg h1, if_neg h2', if_neg h2, sub_zero, mul_zero, add_zero]

/- English proof (translation)
Establish `hc` using `hF a b b a he he.symm`. Simplify using `only [if_pos rfl, ↓reduceIte] at hc`. Establish `hcw : E a b (E b a w) - E b a (E a b w) = (μ a : ℂ) • w - (μ b : ℂ) • w`. Use `congrArg (fun T : Module.End ℂ V => T w) hc` as an intermediate fact. Simplify `this` using `[Module.End.mul_apply, hw a, hw b]`.

Establish `h1 : inner ℂ (E a b w) (E a b w) = inner ℂ w (E b a (E a b w))` using `hU a b he w (E a b w)`. Establish `h2 : inner ℂ (E b a w) (E b a w) = inner ℂ w (E a b (E b a w))` using `hU b a he.symm w (E b a w)`. Establish `h3 : E b a (E a b w) = E a b (E b a w) - ((μ a : ℂ) • w - (μ b : ℂ) • w)`. Rewrite using `[← hcw]`. Normalize the expressions using the abelian group laws.

Rewrite using `[norm_sq_eq_re_inner (𝕜 := ℂ) (E a b w), norm_sq_eq_re_inner (𝕜 := ℂ) (E b a w), norm_sq_eq_re_inner (𝕜 := ℂ) w, h1, h2, h3, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right]`. Simplify using `only [RCLike.re_to_complex, Complex.sub_re, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_identity (hF : KRel ε E) (hU : KUnit ε E) {a b : Fin n} (he : ε a = ε b) {μ : Fin n → ℝ} {w : V}
    (hw : IsWeight E μ w) : ‖E a b w‖ ^ 2 = ‖E b a w‖ ^ 2 + (μ b - μ a) * ‖w‖ ^ 2 := by
  have hc := hF a b b a he he.symm
  simp only [if_pos rfl, ↓reduceIte] at hc
  have hcw : E a b (E b a w) - E b a (E a b w) = (μ a : ℂ) • w - (μ b : ℂ) • w := by
    have := congrArg (fun T : Module.End ℂ V => T w) hc
    simpa [Module.End.mul_apply, hw a, hw b] using this
  have h1 : inner ℂ (E a b w) (E a b w) = inner ℂ w (E b a (E a b w)) := hU a b he w (E a b w)
  have h2 : inner ℂ (E b a w) (E b a w) = inner ℂ w (E a b (E b a w)) := hU b a he.symm w (E b a w)
  have h3 : E b a (E a b w) = E a b (E b a w) - ((μ a : ℂ) • w - (μ b : ℂ) • w) := by
    rw [← hcw]; abel
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (E a b w), norm_sq_eq_re_inner (𝕜 := ℂ) (E b a w),
    norm_sq_eq_re_inner (𝕜 := ℂ) w, h1, h2, h3, inner_sub_right, inner_sub_right, inner_smul_right,
    inner_smul_right]
  simp only [RCLike.re_to_complex, Complex.sub_re, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `norm_identity hF hU he hz` as an intermediate fact. Simplify using `only [pow_zero, Module.End.one_apply, pow_one, Nat.cast_zero, zero_add, one_mul, sub_zero]`. Use polynomial arithmetic with `[sq_nonneg ‖E b a z‖]`.

Consider the case `succ k ih`. Establish `hw1` using `isWeight_pow hF he hz (k + 1)`. Establish `hid` using `norm_identity hF hU he hw1`. Establish `hE2 : (E a b ^ (k + 1 + 1)) z = E a b ((E a b ^ (k + 1)) z)`. Rewrite using `[pow_succ', Module.End.mul_apply]`.

Establish `hE1 : (E a b ^ (k + 1)) z = E a b ((E a b ^ k) z)` using `by rw [pow_succ', Module.End.mul_apply]`. Establish `hsh : shift μ a b (k + 1) b - shift μ a b (k + 1) a = μ b - μ a - 2 * ((k : ℝ) + 1)`. Simplify using `only [shift, if_neg hab, if_neg (Ne.symm hab), if_pos rfl, ↓reduceIte]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcs : ‖(E a b ^ (k + 1)) z‖ ^ 2 ≤ ‖E b a ((E a b ^ (k + 1)) z)‖ * ‖(E a b ^ k) z‖`. Establish `h1 : inner ℂ (E b a ((E a b ^ (k + 1)) z)) ((E a b ^ k) z) = inner ℂ ((E a b ^ (k + 1)) z) ((E a b ^ (k + 1)) z)`. Rewrite using `[hU b a he.symm, ← hE1]`. Establish `h3 : ‖inner ℂ ((E a b ^ (k + 1)) z) ((E a b ^ (k + 1)) z)‖ = ‖(E a b ^ (k + 1)) z‖ ^ 2`. Rewrite using `[inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]`.

Establish `h2` using `norm_inner_le_norm (𝕜 := ℂ) (E b a ((E a b ^ (k + 1)) z)) ((E a b ^ k) z)`. Rewrite `h2` using `[h1, h3]`. Conclude with `h2`. Establish `hn0` using `norm_nonneg ((E a b ^ k) z)`. Establish `hn1` using `norm_nonneg ((E a b ^ (k + 1)) z)`.

Establish `hnA` using `norm_nonneg (E b a ((E a b ^ (k + 1)) z))`. Establish `key : ((k : ℝ) + 1) * (μ b - μ a - k) * ‖(E a b ^ (k + 1)) z‖ ^ 2 ≤ ‖E b a ((E a b ^ (k + 1)) z)‖ ^ 2`. Break down `le_or_gt (((k : ℝ) + 1) * (μ b - μ a - k)) 0 with hc | hc` into its components or cases. Use polynomial arithmetic with `[mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg ‖(E a b ^ (k + 1)) z‖), sq_nonneg ‖E b a ((E a b ^ (k + 1)) z)‖]`. Break down `eq_or_lt_of_le hn0 with h0 | h0` into its components or cases.

Rewrite `hcs` using `[← h0, mul_zero]`. Establish `: ‖(E a b ^ (k + 1)) z‖ = 0` using `by nlinarith`. Rewrite using `[this]`. Use polynomial arithmetic with `[sq_nonneg ‖E b a ((E a b ^ (k + 1)) z)‖]`. Establish `h4 : ((k : ℝ) + 1) * (μ b - μ a - k) * ‖(E a b ^ (k + 1)) z‖ ^ 2 * ‖(E a b ^ k) z‖ ^ 2 ≤ ‖E b a ((E a b ^ (k + 1)) z)‖ ^ 2 * ‖(E a b ^ k) z‖ ^ 2`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left ih (sq_nonneg ‖(E a b ^ (k + 1)) z‖), pow_le_pow_left₀ (sq_nonneg _) hcs 2]`. Conclude with `le_of_mul_le_mul_right h4 (by positivity)`. Rewrite using `[hE2, hid, hsh]`. Use `push_cast`. Use polynomial arithmetic with `[key]`.
-/
lemma string_bound (hF : KRel ε E) (hU : KUnit ε E) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    {μ : Fin n → ℝ} {z : V} (hz : IsWeight E μ z) (k : ℕ) :
    (k + 1) * (μ b - μ a - k) * ‖(E a b ^ k) z‖ ^ 2 ≤ ‖(E a b ^ (k + 1)) z‖ ^ 2 := by
  induction k with
  | zero =>
    have := norm_identity hF hU he hz
    simp only [pow_zero, Module.End.one_apply, pow_one, Nat.cast_zero, zero_add, one_mul, sub_zero]
    nlinarith [sq_nonneg ‖E b a z‖]
  | succ k ih =>
    have hw1 := isWeight_pow hF he hz (k + 1)
    have hid := norm_identity hF hU he hw1
    have hE2 : (E a b ^ (k + 1 + 1)) z = E a b ((E a b ^ (k + 1)) z) := by
      rw [pow_succ', Module.End.mul_apply]
    have hE1 : (E a b ^ (k + 1)) z = E a b ((E a b ^ k) z) := by rw [pow_succ', Module.End.mul_apply]
    have hsh : shift μ a b (k + 1) b - shift μ a b (k + 1) a = μ b - μ a - 2 * ((k : ℝ) + 1) := by
      simp only [shift, if_neg hab, if_neg (Ne.symm hab), if_pos rfl, ↓reduceIte]; push_cast; ring
    have hcs : ‖(E a b ^ (k + 1)) z‖ ^ 2 ≤ ‖E b a ((E a b ^ (k + 1)) z)‖ * ‖(E a b ^ k) z‖ := by
      have h1 : inner ℂ (E b a ((E a b ^ (k + 1)) z)) ((E a b ^ k) z) =
          inner ℂ ((E a b ^ (k + 1)) z) ((E a b ^ (k + 1)) z) := by
        rw [hU b a he.symm, ← hE1]
      have h3 : ‖inner ℂ ((E a b ^ (k + 1)) z) ((E a b ^ (k + 1)) z)‖ = ‖(E a b ^ (k + 1)) z‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
      have h2 := norm_inner_le_norm (𝕜 := ℂ) (E b a ((E a b ^ (k + 1)) z)) ((E a b ^ k) z)
      rw [h1, h3] at h2
      exact h2
    have hn0 := norm_nonneg ((E a b ^ k) z)
    have hn1 := norm_nonneg ((E a b ^ (k + 1)) z)
    have hnA := norm_nonneg (E b a ((E a b ^ (k + 1)) z))
    have key : ((k : ℝ) + 1) * (μ b - μ a - k) * ‖(E a b ^ (k + 1)) z‖ ^ 2 ≤
        ‖E b a ((E a b ^ (k + 1)) z)‖ ^ 2 := by
      rcases le_or_gt (((k : ℝ) + 1) * (μ b - μ a - k)) 0 with hc | hc
      · nlinarith [mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg ‖(E a b ^ (k + 1)) z‖),
          sq_nonneg ‖E b a ((E a b ^ (k + 1)) z)‖]
      · rcases eq_or_lt_of_le hn0 with h0 | h0
        · rw [← h0, mul_zero] at hcs
          have : ‖(E a b ^ (k + 1)) z‖ = 0 := by nlinarith
          rw [this]
          nlinarith [sq_nonneg ‖E b a ((E a b ^ (k + 1)) z)‖]
        · have h4 : ((k : ℝ) + 1) * (μ b - μ a - k) * ‖(E a b ^ (k + 1)) z‖ ^ 2 * ‖(E a b ^ k) z‖ ^ 2 ≤
              ‖E b a ((E a b ^ (k + 1)) z)‖ ^ 2 * ‖(E a b ^ k) z‖ ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_left ih (sq_nonneg ‖(E a b ^ (k + 1)) z‖),
              pow_le_pow_left₀ (sq_nonneg _) hcs 2]
          exact le_of_mul_le_mul_right h4 (by positivity)
    rw [hE2, hid, hsh]
    push_cast
    nlinarith [key]

/- English proof (translation)
Establish `hmem : ∀ k : ℕ, (E a b ^ k) z ∈ L`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using hzL`. Consider the case `succ k ih => rw [pow_succ', Module.End.mul_apply]`.

Conclude with `hL a b he _ ih`. Use `⟨hmem, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hw : ∀ k, IsWeight E (shift μ a b k) ((E a b ^ k) z)` using `isWeight_pow hF he hz`.

Establish `hinj : ∀ k k' : ℕ, k ≠ k' → shift μ a b k ≠ shift μ a b k'`. Introduce `k k' hkk' h`. Use `congrFun h a` as an intermediate fact. Simplify using `only [shift, if_neg hab, ↓reduceIte, sub_zero, mul_one, add_right_inj] at this`. Conclude with `hkk' (by exact_mod_cast this)`.

Set `f : ℕ → L` to `fun k => ⟨(E a b ^ k) z, hmem k⟩`. Establish `hli : LinearIndependent ℂ (L.subtype ∘ f)`. Apply `linearIndependent_of_ne_zero_of_inner_eq_zero` to reduce the goal to its premises. Introduce `k`. Conclude with `hne k`.

Introduce `k k' hkk'`. Conclude with `inner_eq_zero_of_weight hU (hw k) (hw k') (hinj k k' hkk')`. Use `haveI := (LinearIndependent.of_comp L.subtype hli).finite`. Conclude with `not_finite ℕ`.
-/
lemma exists_pow_eq_zero (hF : KRel ε E) (hU : KUnit ε E) {L : Submodule ℂ V} [FiniteDimensional ℂ L]
    (hL : KStab ε E L) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    {μ : Fin n → ℝ} {z : V} (hzL : z ∈ L) (hz : IsWeight E μ z) :
    (∀ k : ℕ, (E a b ^ k) z ∈ L) ∧ ∃ k : ℕ, (E a b ^ k) z = 0 := by
  have hmem : ∀ k : ℕ, (E a b ^ k) z ∈ L := by
    intro k
    induction k with
    | zero => simpa using hzL
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hL a b he _ ih
  refine ⟨hmem, ?_⟩
  by_contra hne
  push Not at hne
  have hw : ∀ k, IsWeight E (shift μ a b k) ((E a b ^ k) z) := isWeight_pow hF he hz
  have hinj : ∀ k k' : ℕ, k ≠ k' → shift μ a b k ≠ shift μ a b k' := by
    intro k k' hkk' h
    have := congrFun h a
    simp only [shift, if_neg hab, ↓reduceIte, sub_zero, mul_one, add_right_inj] at this
    exact hkk' (by exact_mod_cast this)
  let f : ℕ → L := fun k => ⟨(E a b ^ k) z, hmem k⟩
  have hli : LinearIndependent ℂ (L.subtype ∘ f) := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro k; exact hne k
    · intro k k' hkk'
      exact inner_eq_zero_of_weight hU (hw k) (hw k') (hinj k k' hkk')
  haveI := (LinearIndependent.of_comp L.subtype hli).finite
  exact not_finite ℕ

/- English proof (translation)
Take `⟨hmemz, hex⟩` from `exists_pow_eq_zero hF hU hL hab he hzL hz`. Take `⟨K, hK, hKmin⟩ : ∃ K, (E a b ^ K) z = 0 ∧ ∀ m < K, (E a b ^ m) z ≠ 0` from `⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩`. Establish `hK0 : K ≠ 0`. Introduce and unpack `rfl`. Rewrite `hK` using `[pow_zero, Module.End.one_apply]`.

Conclude with `hz0 hK`. Take `⟨K', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hK0`. Establish `hu0 : (E a b ^ K') z ≠ 0` using `hKmin K' (Nat.lt_succ_self _)`. Establish `huL : (E a b ^ K') z ∈ L` using `hmemz K'`. Establish `hEu : E a b ((E a b ^ K') z) = 0`.

Rewrite using `[← Module.End.mul_apply, ← pow_succ']`. Conclude with `hK`. Establish `hνu : IsWeight E (shift μ a b K') ((E a b ^ K') z)` using `isWeight_pow hF he hz K'`. Establish `hupos : 0 < ‖(E a b ^ K') z‖ ^ 2` using `pow_pos (norm_pos_iff.mpr hu0) 2`. Establish `hdle : μ b - μ a ≤ K'`.

Establish `hsb` using `string_bound hF hU hab he hz K'`. Rewrite `hsb` using `[hK, norm_zero]`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `: 0 < ((K' : ℝ) + 1) * (μ b - μ a - K') * ‖(E a b ^ K') z‖ ^ 2` using `mul_pos (mul_pos (by positivity) (by linarith)) hupos`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hνa : shift μ a b K' a = μ a + K'`. Simplify using `only [shift, if_neg hab, ↓reduceIte]`. Expand and normalize the polynomial expressions, which then agree. Establish `hνb : shift μ a b K' b = μ b - K'`.

Simplify using `only [shift, if_neg (Ne.symm hab), ↓reduceIte]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlow : ∀ j : ℕ, E a b ((E b a ^ (j + 1)) ((E a b ^ K') z)) = (((((j : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - j)) : ℝ) : ℂ) • (E b a ^ j) ((E a b ^ K') z)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Rewrite using `[zero_add, pow_one, kcomm_apply hF he he.symm, hEu, map_zero, zero_add]`. Simplify using `only [if_pos rfl, ↓reduceIte, pow_zero, Module.End.one_apply, hνu a, hνu b]`. Rewrite using `[← sub_smul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ j ih`. Rewrite using `[pow_succ' (E b a) (j + 1), Module.End.mul_apply, kcomm_apply hF he he.symm, ih, map_smul]`. Simplify using `only [if_pos rfl, ↓reduceIte]`.

Establish `hwj` using `isWeight_pow hF he.symm hνu (j + 1)`. Rewrite using `[hwj a, hwj b, ← Module.End.mul_apply (E b a), ← pow_succ', ← sub_smul, ← add_smul]`. Use `congr 1`. Simplify using `only [shift, if_neg hab, if_neg (Ne.symm hab), if_pos rfl, ↓reduceIte]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hnormlow : ∀ j : ℕ, ‖(E b a ^ (j + 1)) ((E a b ^ K') z)‖ ^ 2 = ((j : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - j) * ‖(E b a ^ j) ((E a b ^ K') z)‖ ^ 2`. Introduce `j`. Establish `hy : (E b a ^ (j + 1)) ((E a b ^ K') z) = E b a ((E b a ^ j) ((E a b ^ K') z))`. Rewrite using `[pow_succ', Module.End.mul_apply]`.

Establish `h1 : inner ℂ ((E b a ^ (j + 1)) ((E a b ^ K') z)) ((E b a ^ (j + 1)) ((E a b ^ K') z)) = (((((j : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - j)) : ℝ) : ℂ) * inner ℂ ((E b a ^ j) ((E a b ^ K') z)) ((E b a ^ j) ((E a b ^ K') z))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hy]`. Use `_ = inner ℂ (E a b ((E b a ^ (j + 1)) ((E a b ^ K') z))) ((E b a ^ j) ((E a b ^ K') z)) := (hU a b he _ _).symm`. Use `_ = _ := by rw [hlow j, inner_smul_left, Complex.conj_ofReal]`.

Establish `h2` using `congrArg Complex.re h1`. Rewrite `h2` using `[Complex.re_ofReal_mul]`. Rewrite using `[norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ) ((E b a ^ j) ((E a b ^ K') z)), RCLike.re_to_complex, RCLike.re_to_complex]`. Conclude with `h2`. Take `⟨_, hexJ⟩` from `exists_pow_eq_zero hF hU hL (Ne.symm hab) he.symm huL hνu`.

Take `⟨J, hJ, hJmin⟩ : ∃ J, (E b a ^ J) ((E a b ^ K') z) = 0 ∧ ∀ m < J, (E b a ^ m) ((E a b ^ K') z) ≠ 0` from `⟨Nat.find hexJ, Nat.find_spec hexJ, fun m hm => Nat.find_min hexJ hm⟩`. Establish `hJ0 : J ≠ 0`. Introduce and unpack `rfl`. Rewrite `hJ` using `[pow_zero, Module.End.one_apply]`. Conclude with `hu0 hJ`.

Take `⟨J', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hJ0`. Establish `hyJ : 0 < ‖(E b a ^ J') ((E a b ^ K') z)‖ ^ 2` using `pow_pos (norm_pos_iff.mpr (hJmin J' (Nat.lt_succ_self _))) 2`. Establish `hNJ : shift μ a b K' a - shift μ a b K' b = J'`. Establish `h` using `hnormlow J'`. Rewrite `h` using `[hJ, norm_zero, zero_pow two_ne_zero]`.

Establish `h' : ((J' : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - J') = 0`. Break down `mul_eq_zero.mp h.symm with h2 | h2` into its components or cases. Conclude with `h2`. Conclude with `absurd h2 (ne_of_gt hyJ)`. Break down `mul_eq_zero.mp h' with h3 | h3` into its components or cases.

Establish `: (0 : ℝ) < (J' : ℝ) + 1` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hNJ` using `[hνa, hνb]`. Establish `hJle : J' ≤ 2 * K'`.

Establish `: (J' : ℝ) ≤ 2 * K'` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `hmR : ((2 * K' - J' : ℕ) : ℝ) = μ b - μ a`. Rewrite using `[Nat.cast_sub hJle]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmle : 2 * K' - J' < K' + 1`. Establish `: ((2 * K' - J' : ℕ) : ℝ) ≤ K'` using `by rw [hmR]; exact hdle`. Establish `: 2 * K' - J' ≤ K'` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers.

Use `⟨(E a b ^ (2 * K' - J')) z, hmemz _, hKmin _ hmle, ?_⟩` and prove the remaining obligations. Establish `hsw : (μ ∘ Equiv.swap a b) = shift μ a b (2 * K' - J')`. Use function extensionality and compare the values at `c`. Simplify using `only [Function.comp_apply, shift]`. Distinguish the cases in `hca : c = a`.

Substitute `hca` using the available equality. Rewrite using `[Equiv.swap_apply_left]`. Simplify using `only [if_pos rfl, ↓reduceIte, if_neg hab, sub_zero, mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hcb : c = b`.

Substitute `hcb` using the available equality. Rewrite using `[Equiv.swap_apply_right]`. Simplify using `only [if_pos rfl, ↓reduceIte, if_neg hca, zero_sub, mul_neg, mul_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Equiv.swap_apply_of_ne_of_ne hca hcb]`.

Simplify using `only [if_neg hca, if_neg hcb, sub_zero, mul_zero, add_zero]`. Rewrite using `[hsw]`. Conclude with `isWeight_pow hF he hz _`.
-/
lemma swap_weight_of_le (hF : KRel ε E) (hU : KUnit ε E) {L : Submodule ℂ V} [FiniteDimensional ℂ L]
    (hL : KStab ε E L) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    {μ : Fin n → ℝ} {z : V} (hzL : z ∈ L) (hz0 : z ≠ 0) (hz : IsWeight E μ z) (hle : μ a ≤ μ b) :
    ∃ z' ∈ L, z' ≠ 0 ∧ IsWeight E (μ ∘ Equiv.swap a b) z' := by
  classical
  obtain ⟨hmemz, hex⟩ := exists_pow_eq_zero hF hU hL hab he hzL hz
  obtain ⟨K, hK, hKmin⟩ : ∃ K, (E a b ^ K) z = 0 ∧ ∀ m < K, (E a b ^ m) z ≠ 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hK0 : K ≠ 0 := by
    rintro rfl
    rw [pow_zero, Module.End.one_apply] at hK
    exact hz0 hK
  obtain ⟨K', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK0
  have hu0 : (E a b ^ K') z ≠ 0 := hKmin K' (Nat.lt_succ_self _)
  have huL : (E a b ^ K') z ∈ L := hmemz K'
  have hEu : E a b ((E a b ^ K') z) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ']; exact hK
  have hνu : IsWeight E (shift μ a b K') ((E a b ^ K') z) := isWeight_pow hF he hz K'
  have hupos : 0 < ‖(E a b ^ K') z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
  have hdle : μ b - μ a ≤ K' := by
    have hsb := string_bound hF hU hab he hz K'
    rw [hK, norm_zero] at hsb
    by_contra hcon
    push Not at hcon
    have : 0 < ((K' : ℝ) + 1) * (μ b - μ a - K') * ‖(E a b ^ K') z‖ ^ 2 :=
      mul_pos (mul_pos (by positivity) (by linarith)) hupos
    nlinarith
  have hνa : shift μ a b K' a = μ a + K' := by
    simp only [shift, if_neg hab, ↓reduceIte]; ring
  have hνb : shift μ a b K' b = μ b - K' := by
    simp only [shift, if_neg (Ne.symm hab), ↓reduceIte]; ring
  have hlow : ∀ j : ℕ, E a b ((E b a ^ (j + 1)) ((E a b ^ K') z)) =
      (((((j : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - j)) : ℝ) : ℂ) • (E b a ^ j) ((E a b ^ K') z) := by
    intro j
    induction j with
    | zero =>
      rw [zero_add, pow_one, kcomm_apply hF he he.symm, hEu, map_zero, zero_add]
      simp only [if_pos rfl, ↓reduceIte, pow_zero, Module.End.one_apply, hνu a, hνu b]
      rw [← sub_smul]
      congr 1
      push_cast
      ring
    | succ j ih =>
      rw [pow_succ' (E b a) (j + 1), Module.End.mul_apply, kcomm_apply hF he he.symm, ih, map_smul]
      simp only [if_pos rfl, ↓reduceIte]
      have hwj := isWeight_pow hF he.symm hνu (j + 1)
      rw [hwj a, hwj b, ← Module.End.mul_apply (E b a), ← pow_succ', ← sub_smul, ← add_smul]
      congr 1
      simp only [shift, if_neg hab, if_neg (Ne.symm hab), if_pos rfl, ↓reduceIte]
      push_cast
      ring
  have hnormlow : ∀ j : ℕ, ‖(E b a ^ (j + 1)) ((E a b ^ K') z)‖ ^ 2 =
      ((j : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - j) * ‖(E b a ^ j) ((E a b ^ K') z)‖ ^ 2 := by
    intro j
    have hy : (E b a ^ (j + 1)) ((E a b ^ K') z) = E b a ((E b a ^ j) ((E a b ^ K') z)) := by
      rw [pow_succ', Module.End.mul_apply]
    have h1 : inner ℂ ((E b a ^ (j + 1)) ((E a b ^ K') z)) ((E b a ^ (j + 1)) ((E a b ^ K') z)) =
        (((((j : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - j)) : ℝ) : ℂ) *
          inner ℂ ((E b a ^ j) ((E a b ^ K') z)) ((E b a ^ j) ((E a b ^ K') z)) := by
      calc inner ℂ ((E b a ^ (j + 1)) ((E a b ^ K') z)) ((E b a ^ (j + 1)) ((E a b ^ K') z))
          = inner ℂ ((E b a ^ (j + 1)) ((E a b ^ K') z)) (E b a ((E b a ^ j) ((E a b ^ K') z))) := by
            rw [← hy]
        _ = inner ℂ (E a b ((E b a ^ (j + 1)) ((E a b ^ K') z))) ((E b a ^ j) ((E a b ^ K') z)) :=
            (hU a b he _ _).symm
        _ = _ := by rw [hlow j, inner_smul_left, Complex.conj_ofReal]
    have h2 := congrArg Complex.re h1
    rw [Complex.re_ofReal_mul] at h2
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ) ((E b a ^ j) ((E a b ^ K') z)),
      RCLike.re_to_complex, RCLike.re_to_complex]
    exact h2
  obtain ⟨_, hexJ⟩ := exists_pow_eq_zero hF hU hL (Ne.symm hab) he.symm huL hνu
  obtain ⟨J, hJ, hJmin⟩ : ∃ J, (E b a ^ J) ((E a b ^ K') z) = 0 ∧ ∀ m < J, (E b a ^ m) ((E a b ^ K') z) ≠ 0 :=
    ⟨Nat.find hexJ, Nat.find_spec hexJ, fun m hm => Nat.find_min hexJ hm⟩
  have hJ0 : J ≠ 0 := by
    rintro rfl
    rw [pow_zero, Module.End.one_apply] at hJ
    exact hu0 hJ
  obtain ⟨J', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ0
  have hyJ : 0 < ‖(E b a ^ J') ((E a b ^ K') z)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (hJmin J' (Nat.lt_succ_self _))) 2
  have hNJ : shift μ a b K' a - shift μ a b K' b = J' := by
    have h := hnormlow J'
    rw [hJ, norm_zero, zero_pow two_ne_zero] at h
    have h' : ((J' : ℝ) + 1) * (shift μ a b K' a - shift μ a b K' b - J') = 0 := by
      rcases mul_eq_zero.mp h.symm with h2 | h2
      · exact h2
      · exact absurd h2 (ne_of_gt hyJ)
    rcases mul_eq_zero.mp h' with h3 | h3
    · have : (0 : ℝ) < (J' : ℝ) + 1 := by positivity
      linarith
    · linarith
  rw [hνa, hνb] at hNJ
  have hJle : J' ≤ 2 * K' := by
    have : (J' : ℝ) ≤ 2 * K' := by linarith
    exact_mod_cast this
  have hmR : ((2 * K' - J' : ℕ) : ℝ) = μ b - μ a := by
    rw [Nat.cast_sub hJle]
    push_cast
    linarith
  have hmle : 2 * K' - J' < K' + 1 := by
    have : ((2 * K' - J' : ℕ) : ℝ) ≤ K' := by rw [hmR]; exact hdle
    have : 2 * K' - J' ≤ K' := by exact_mod_cast this
    omega
  refine ⟨(E a b ^ (2 * K' - J')) z, hmemz _, hKmin _ hmle, ?_⟩
  have hsw : (μ ∘ Equiv.swap a b) = shift μ a b (2 * K' - J') := by
    funext c
    simp only [Function.comp_apply, shift]
    by_cases hca : c = a
    · subst hca
      rw [Equiv.swap_apply_left]
      simp only [if_pos rfl, ↓reduceIte, if_neg hab, sub_zero, mul_one]
      linarith
    · by_cases hcb : c = b
      · subst hcb
        rw [Equiv.swap_apply_right]
        simp only [if_pos rfl, ↓reduceIte, if_neg hca, zero_sub, mul_neg, mul_one]
        linarith
      · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
        simp only [if_neg hca, if_neg hcb, sub_zero, mul_zero, add_zero]
  rw [hsw]
  exact isWeight_pow hF he hz _

/- English proof (translation)
Break down `le_total (μ a) (μ b) with h | h` into its components or cases. Conclude with `swap_weight_of_le hF hU hL hab he hzL hz0 hz h`. Take `⟨z', hz'L, hz'0, hz'⟩` from `swap_weight_of_le hF hU hL (Ne.symm hab) he.symm hzL hz0 hz h`. Conclude with `⟨z', hz'L, hz'0, by rwa [Equiv.swap_comm] at hz'⟩`.
-/
lemma swap_weight (hF : KRel ε E) (hU : KUnit ε E) {L : Submodule ℂ V} [FiniteDimensional ℂ L]
    (hL : KStab ε E L) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    {μ : Fin n → ℝ} {z : V} (hzL : z ∈ L) (hz0 : z ≠ 0) (hz : IsWeight E μ z) :
    ∃ z' ∈ L, z' ≠ 0 ∧ IsWeight E (μ ∘ Equiv.swap a b) z' := by
  rcases le_total (μ a) (μ b) with h | h
  · exact swap_weight_of_le hF hU hL hab he hzL hz0 hz h
  · obtain ⟨z', hz'L, hz'0, hz'⟩ := swap_weight_of_le hF hU hL (Ne.symm hab) he.symm hzL hz0 hz h
    exact ⟨z', hz'L, hz'0, by rwa [Equiv.swap_comm] at hz'⟩

/- English proof (translation)
Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `w hw hεw μ z hzL hz0 hz`. Distinguish the cases in `h1 : w = 1`.

Substitute `h1` using the available equality. Conclude with `⟨z, hzL, hz0, by simpa using hz⟩`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, w x ≠ x := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Conclude with `h1 (Equiv.ext hcon)`. Establish `hlt` using `Equiv.Perm.card_support_swap_mul hx`. Take `⟨z1, hz1L, hz10, hz1⟩` from `swap_weight hF hU hL (Ne.symm hx) (hεw x).symm hzL hz0 hz`. Establish `hεw' : ∀ c, ε ((Equiv.swap x (w x) * w) c) = ε c`. Introduce `c`.

Rewrite using `[Equiv.Perm.mul_apply, Equiv.swap_apply_def]`. Use `split_ifs with h2 h3`. Rewrite using `[hεw x, ← h2, hεw c]`. Rewrite using `[← hεw x, ← h3, hεw c]`. Conclude with `hεw c`.

Take `⟨z', hz'L, hz'0, hz'⟩` from `ih _ (hw ▸ hlt) (Equiv.swap x (w x) * w) rfl hεw' hz1L hz10 hz1`. Use `⟨z', hz'L, hz'0, ?_⟩` and prove the remaining obligations. Establish `heq : (μ ∘ Equiv.swap x (w x)) ∘ (Equiv.swap x (w x) * w) = μ ∘ w`. Use function extensionality and compare the values at `c`. Simplify using `only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_self]`.

Rewrite `hz'` using `[heq]`. Then use the resulting hypothesis.
-/
lemma perm_weight (hF : KRel ε E) (hU : KUnit ε E) {L : Submodule ℂ V} [FiniteDimensional ℂ L]
    (hL : KStab ε E L) : ∀ (m : ℕ) (w : Equiv.Perm (Fin n)), w.support.card = m → (∀ c, ε (w c) = ε c) →
      ∀ {μ : Fin n → ℝ} {z : V}, z ∈ L → z ≠ 0 → IsWeight E μ z →
        ∃ z' ∈ L, z' ≠ 0 ∧ IsWeight E (μ ∘ w) z' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro w hw hεw μ z hzL hz0 hz
    by_cases h1 : w = 1
    · subst h1
      exact ⟨z, hzL, hz0, by simpa using hz⟩
    · obtain ⟨x, hx⟩ : ∃ x, w x ≠ x := by
        by_contra hcon
        push Not at hcon
        exact h1 (Equiv.ext hcon)
      have hlt := Equiv.Perm.card_support_swap_mul hx
      obtain ⟨z1, hz1L, hz10, hz1⟩ := swap_weight hF hU hL (Ne.symm hx) (hεw x).symm hzL hz0 hz
      have hεw' : ∀ c, ε ((Equiv.swap x (w x) * w) c) = ε c := by
        intro c
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
        split_ifs with h2 h3
        · rw [hεw x, ← h2, hεw c]
        · rw [← hεw x, ← h3, hεw c]
        · exact hεw c
      obtain ⟨z', hz'L, hz'0, hz'⟩ := ih _ (hw ▸ hlt) (Equiv.swap x (w x) * w) rfl hεw' hz1L hz10 hz1
      refine ⟨z', hz'L, hz'0, ?_⟩
      have heq : (μ ∘ Equiv.swap x (w x)) ∘ (Equiv.swap x (w x) * w) = μ ∘ w := by
        funext c
        simp only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_self]
      rwa [heq] at hz'

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Establish `key : ∀ a b : Fin n, (if ε a = ε b then F a b * F b a else 0) * F c d - F c d * (if ε a = ε b then F a b * F b a else 0) = (if ε a = ε b ∧ a = c then F a b * F b d else 0) - (if ε a = ε b ∧ d = b then F a b * F c a else 0) + ((if ε a = ε b ∧ b = c then F a d * F b a else 0) - (if …`. Introduce `a b`. Distinguish the cases in `hab : ε a = ε b`. Establish `h1` using `hF b a c d hab.symm hcd`.

Establish `h2` using `hF a b c d hab hcd`. Establish `h3 : F a b * F b a * F c d - F c d * (F a b * F b a) = F a b * (F b a * F c d - F c d * F b a) + (F a b * F c d - F c d * F a b) * F b a` using `by noncomm_ring`. Rewrite using `[if_pos hab, h3, h1, h2]`. Simplify using `only [hab, true_and, mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]`. Simplify using `[hab]`.

Unfold `CasK`. Simplify using `only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Simplify using `only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Establish `e1 : ∑ a, ∑ b, (if ε a = ε b ∧ a = c then F a b * F b d else 0) = ∑ b, (if ε c = ε b then F c b * F b d else 0)`. Rewrite using `[Fintype.sum_eq_single c]`.

Simplify using the standard rewrite rules. Introduce `a ha`. Simplify using `[ha]`. Establish `e4 : ∑ a, ∑ b, (if ε a = ε b ∧ d = a then F c b * F b a else 0) = ∑ b, (if ε c = ε b then F c b * F b d else 0)`. Rewrite using `[Fintype.sum_eq_single d]`.

Simplify using `[hcd]`. Introduce `a ha`. Simplify using `[Ne.symm ha]`. Establish `e2 : ∑ a, ∑ b, (if ε a = ε b ∧ d = b then F a b * F c a else 0) = ∑ a, (if ε a = ε c then F a d * F c a else 0)`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Fintype.sum_eq_single d]`. Simplify using `[hcd]`. Introduce `b hb`. Simplify using `[Ne.symm hb]`. Establish `e3 : ∑ a, ∑ b, (if ε a = ε b ∧ b = c then F a d * F b a else 0) = ∑ a, (if ε a = ε c then F a d * F c a else 0)`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_eq_single c]`. Simplify using the standard rewrite rules. Introduce `b hb`. Simplify using `[hb]`.

Rewrite using `[e1, e2, e3, e4]`. Normalize the expressions using the abelian group laws.
-/
private lemma casK_mul_comm_of_eq_sign {A : Type} [Ring A] {F : Fin n → Fin n → A} (hF : KRel ε F) {c d : Fin n}
    (hcd : ε c = ε d) : CasK ε F * F c d = F c d * CasK ε F := by
  rw [← sub_eq_zero]
  have key : ∀ a b : Fin n, (if ε a = ε b then F a b * F b a else 0) * F c d -
      F c d * (if ε a = ε b then F a b * F b a else 0) =
      (if ε a = ε b ∧ a = c then F a b * F b d else 0) - (if ε a = ε b ∧ d = b then F a b * F c a else 0) +
      ((if ε a = ε b ∧ b = c then F a d * F b a else 0) - (if ε a = ε b ∧ d = a then F c b * F b a else 0)) := by
    intro a b
    by_cases hab : ε a = ε b
    · have h1 := hF b a c d hab.symm hcd
      have h2 := hF a b c d hab hcd
      have h3 : F a b * F b a * F c d - F c d * (F a b * F b a) =
          F a b * (F b a * F c d - F c d * F b a) + (F a b * F c d - F c d * F a b) * F b a := by
        noncomm_ring
      rw [if_pos hab, h3, h1, h2]
      simp only [hab, true_and, mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
    · simp [hab]
  unfold CasK
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ a, ∑ b, (if ε a = ε b ∧ a = c then F a b * F b d else 0) =
      ∑ b, (if ε c = ε b then F c b * F b d else 0) := by
    rw [Fintype.sum_eq_single c]
    · simp
    · intro a ha; simp [ha]
  have e4 : ∑ a, ∑ b, (if ε a = ε b ∧ d = a then F c b * F b a else 0) =
      ∑ b, (if ε c = ε b then F c b * F b d else 0) := by
    rw [Fintype.sum_eq_single d]
    · simp [hcd]
    · intro a ha; simp [Ne.symm ha]
  have e2 : ∑ a, ∑ b, (if ε a = ε b ∧ d = b then F a b * F c a else 0) =
      ∑ a, (if ε a = ε c then F a d * F c a else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_eq_single d]
    · simp [hcd]
    · intro b hb; simp [Ne.symm hb]
  have e3 : ∑ a, ∑ b, (if ε a = ε b ∧ b = c then F a d * F b a else 0) =
      ∑ a, (if ε a = ε c then F a d * F c a else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_eq_single c]
    · simp
    · intro b hb; simp [hb]
  rw [e1, e2, e3, e4]
  abel

/- English proof (translation)
Establish `hterm : ∀ a b : Fin n, (if ε a = ε b then E a b * E b a else 0) y = (((if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ)) : ℂ) • y`. Introduce `a b`. Distinguish the cases in `hab : ε a = ε b`. Simplify using `only [if_pos hab, Module.End.mul_apply]`. Break down `lt_trichotomy a b with hlt | heq | hgt` into its components or cases.

Rewrite using `[if_neg hlt.ne, if_pos hlt, ReciprocityTheory.ChartRestriction.DS.HW.lie_relation_raise_lower hF hab, hy.2 a b hlt hab, map_zero, zero_add, hy.1 a, hy.1 b, ← sub_smul, Complex.ofReal_sub]`. Substitute `heq` using the available equality. Rewrite using `[if_pos rfl, hy.1 a, map_smul, hy.1 a, smul_smul, Complex.ofReal_pow, sq]`. Rewrite using `[if_neg hgt.ne', if_neg (not_lt.mpr hgt.le), hy.2 b a hgt hab.symm, map_zero]`. Simplify using the standard rewrite rules.

Simplify using `[hab]`. Establish `hsum : ∑ a, ∑ b, (if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ) = PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε)`. Establish `h2ρ : ∀ a, 2 * PI.UpqRep.rhoC ε a = ∑ b, (if a < b ∧ ε b = ε a then (1 : ℝ) else 0) - ∑ b, (if b < a ∧ ε b = ε a then (1 : ℝ) else 0)`. Introduce `a`. Simplify using `only [PI.UpqRep.rhoC, Finset.sum_boole]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hR : PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε) = ∑ a, ν a ^ 2 + (∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν a else 0) - ∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν b else 0))`. Establish `e1 : PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε) = ∑ a, (ν a ^ 2 + ν a * (2 * PI.UpqRep.rhoC ε a))`. Simplify using `only [PI.UpqRep.nsq, PI.UpqRep.dot, Pi.add_apply, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`.

Establish `e2 : ∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν a else 0) = ∑ a, ν a * ∑ b, (if a < b ∧ ε b = ε a then (1 : ℝ) else 0)`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : ε a = ε b`.

Simplify using `[h]`. Simplify using `[h, Ne.symm h]`. Establish `e3 : ∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν b else 0) = ∑ a, ν a * ∑ b, (if b < a ∧ ε b = ε a then (1 : ℝ) else 0)`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[e1, e2, e3]`. Simplify using `only [h2ρ, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]`.

Rewrite using `[hR]`. Establish `hL : ∀ a, ∑ b, (if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ) = ν a ^ 2 + (∑ b, (if a < b ∧ ε a = ε b then ν a else 0) - ∑ b, (if a < b ∧ ε a = ε b then ν b else 0))`. Introduce `a`. Rewrite using `[← Finset.sum_sub_distrib]`. Establish `hb : ∀ b, (if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ) = (if b = a then ν a ^ 2 else 0) + ((if a < b ∧ ε a = ε b then ν a else 0) - (if a < b ∧ ε a = ε b then ν b else 0))`.

Introduce `b`. Distinguish the cases in `hba : b = a`. Substitute `hba` using the available equality. Simplify using the standard rewrite rules. Distinguish the cases in `h : ε a = ε b`.

Distinguish the cases in `hlt : a < b`. Simplify using `[h, hlt, Ne.symm hba, hba]`. Simplify using `[h, hlt, Ne.symm hba, hba]`. Simplify using `[h, hba]`. Rewrite using `[Finset.sum_congr rfl fun b _ => hb b, Finset.sum_add_distrib, Finset.sum_ite_eq']`.

Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl fun a _ => hL a, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Unfold `CasK`. Rewrite using `[← hsum]`. Simplify using `only [LinearMap.sum_apply, hterm, Complex.ofReal_sum, Finset.sum_smul]`.
-/
private lemma casK_apply_eq_of_kHighest (hF : KRel ε E) {ν : Fin n → ℝ} {y : V} (hy : KHighest ε E ν y) :
    CasK ε E y = ((PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε) : ℝ) : ℂ) • y := by
  classical
  have hterm : ∀ a b : Fin n, (if ε a = ε b then E a b * E b a else 0) y =
      (((if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ)) : ℂ) • y := by
    intro a b
    by_cases hab : ε a = ε b
    · simp only [if_pos hab, Module.End.mul_apply]
      rcases lt_trichotomy a b with hlt | heq | hgt
      · rw [if_neg hlt.ne, if_pos hlt, ReciprocityTheory.ChartRestriction.DS.HW.lie_relation_raise_lower hF hab, hy.2 a b hlt hab, map_zero,
          zero_add, hy.1 a, hy.1 b, ← sub_smul, Complex.ofReal_sub]
      · subst heq
        rw [if_pos rfl, hy.1 a, map_smul, hy.1 a, smul_smul, Complex.ofReal_pow, sq]
      · rw [if_neg hgt.ne', if_neg (not_lt.mpr hgt.le), hy.2 b a hgt hab.symm, map_zero]
        simp
    · simp [hab]
  have hsum : ∑ a, ∑ b, (if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ) =
      PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε) := by
    have h2ρ : ∀ a, 2 * PI.UpqRep.rhoC ε a =
        ∑ b, (if a < b ∧ ε b = ε a then (1 : ℝ) else 0) - ∑ b, (if b < a ∧ ε b = ε a then (1 : ℝ) else 0) := by
      intro a
      simp only [PI.UpqRep.rhoC, Finset.sum_boole]
      ring
    have hR : PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε) =
        ∑ a, ν a ^ 2 + (∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν a else 0) -
          ∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν b else 0)) := by
      have e1 : PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε) =
          ∑ a, (ν a ^ 2 + ν a * (2 * PI.UpqRep.rhoC ε a)) := by
        simp only [PI.UpqRep.nsq, PI.UpqRep.dot, Pi.add_apply, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      have e2 : ∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν a else 0) =
          ∑ a, ν a * ∑ b, (if a < b ∧ ε b = ε a then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases h : ε a = ε b
        · simp [h]
        · simp [h, Ne.symm h]
      have e3 : ∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν b else 0) =
          ∑ a, ν a * ∑ b, (if b < a ∧ ε b = ε a then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp
      rw [e1, e2, e3]
      simp only [h2ρ, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hR]
    have hL : ∀ a, ∑ b, (if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ) =
        ν a ^ 2 + (∑ b, (if a < b ∧ ε a = ε b then ν a else 0) - ∑ b, (if a < b ∧ ε a = ε b then ν b else 0)) := by
      intro a
      rw [← Finset.sum_sub_distrib]
      have hb : ∀ b, (if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ) =
          (if b = a then ν a ^ 2 else 0) +
            ((if a < b ∧ ε a = ε b then ν a else 0) - (if a < b ∧ ε a = ε b then ν b else 0)) := by
        intro b
        by_cases hba : b = a
        · subst hba; simp
        · by_cases h : ε a = ε b
          · by_cases hlt : a < b
            · simp [h, hlt, Ne.symm hba, hba]
            · simp [h, hlt, Ne.symm hba, hba]
          · simp [h, hba]
      rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    rw [Finset.sum_congr rfl fun a _ => hL a, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  unfold CasK
  rw [← hsum]
  simp only [LinearMap.sum_apply, hterm, Complex.ofReal_sum, Finset.sum_smul]

/- English proof (translation)
Unfold `CompanionTheory.D.LK.WtMajor`. Introduce `n ε V _ _ E hF hU hLF μ s x hx0 hxw hcas`. Take `⟨S, hSfd, hSst, hxS⟩` from `hLF x`. Establish `main : ∀ (N : ℕ) (T : Submodule ℂ V), Module.finrank ℂ T = N → FiniteDimensional ℂ T → KStab ε E T → (∀ v ∈ T, CasK ε E v = s • v) → x ∈ T → ∃ ν y, y ≠ 0 ∧ KHighest ε E ν y ∧ s = ↑(PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε)) ∧ (∀ c d : Fin n, c < d → …`. Introduce `N`.

Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Introduce `T hN hTfd hTst hTcas hxT`. Use `haveI : FiniteDimensional ℂ T := hTfd`. Establish `hTne : T ≠ ⊥`.

Introduce `h`. Rewrite `hxT` using `[h]`. Conclude with `hx0 ((Submodule.mem_bot ℂ).mp hxT)`. Take `⟨y, hyT, hy0, ν, hyH⟩` from `Formalism.REAL.highestWeightExists_holds V n ε E T hTfd hF hU hTst hTne`. Take `⟨L, hLT, hyL, hLst, -, hLdom, -⟩` from `hlow n ε V E ν y T hF hU hy0 hyH hTfd hTst hyT`.

Use `haveI : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLT`. Take `⟨xL, hxL, xp, hxp, hxsplit⟩` from `Submodule.exists_add_mem_mem_orthogonal (K := L) x`. Establish `hLpst` using `kstab_orthogonal hU hLst`. Establish `hsplit : ∀ (A : Module.End ℂ V) (c : ℂ), (∀ v ∈ L, A v ∈ L) → (∀ v ∈ Lᗮ, A v ∈ Lᗮ) → A x = c • x → A xL = c • xL`. Introduce `A c hAL hAp hAx`.

Establish `h1 : A xL - c • xL ∈ L` using `L.sub_mem (hAL _ hxL) (L.smul_mem _ hxL)`. Establish `h0 : A xL + A xp = c • xL + c • xp`. Rewrite using `[← map_add, ← smul_add, ← hxsplit, hAx]`. Establish `h2 : A xL - c • xL = -(A xp - c • xp)`. Rewrite using `[neg_sub, sub_eq_sub_iff_add_eq_add, add_comm (c • xp)]`.

Conclude with `h0`. Establish `h3 : A xL - c • xL ∈ Lᗮ`. Rewrite using `[h2]`. Conclude with `Lᗮ.neg_mem (Lᗮ.sub_mem (hAp _ hxp) (Lᗮ.smul_mem _ hxp))`. Conclude with `sub_eq_zero.mp (inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal h1 h3))`.

Distinguish the cases in `hxL0 : xL = 0`. Establish `hxp' : x ∈ Lᗮ` using `by rw [hxsplit, hxL0, zero_add]; exact hxp`. Establish `hlt : T ⊓ Lᗮ < T`. Use `lt_of_le_of_ne inf_le_left fun h => hy0 ?_` and prove the remaining obligations. Establish `hy' : y ∈ T ⊓ Lᗮ` using `by rw [h]; exact hyT`.

Conclude with `inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hyL (Submodule.mem_inf.mp hy').2)`. Establish `hlt'` using `Submodule.finrank_lt_finrank_of_lt hlt`. Use `ih _ (hN ▸ hlt') (T ⊓ Lᗮ) rfl (Submodule.finiteDimensional_of_le inf_le_left) ?_ ?_ (Submodule.mem_inf.mpr ⟨hxT, hxp'⟩)` and prove the remaining obligations. Introduce `a b hab v hv`. Conclude with `Submodule.mem_inf.mpr ⟨hTst a b hab v (Submodule.mem_inf.mp hv).1, hLpst a b hab v (Submodule.mem_inf.mp hv).2⟩`.

Introduce `v hv`. Conclude with `hTcas v (Submodule.mem_inf.mp hv).1`. Establish `hxLw : IsWeight E μ xL` using `fun a => hsplit (E a a) (μ a) (fun v hv => hLst a a rfl v hv) (fun v hv => hLpst a a rfl v hv) (hxw a)`. Establish `hform` using `casK_apply_eq_of_kHighest hF hyH`. Rewrite `hform` using `[hTcas y hyT]`.

Establish `hs : s = ↑(PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε))` using `smul_left_injective ℂ hy0 hform`. Use `⟨ν, y, hy0, hyH, hs, ?_, ?_⟩` and prove the remaining obligations. Introduce `c d hcd he`. Establish `hid` using `norm_identity hF hU he hyH.1`. Rewrite `hid` using `[hyH.2 c d hcd he, norm_zero]`.

Establish `hy2 : 0 < ‖y‖ ^ 2` using `pow_pos (norm_pos_iff.mpr hy0) 2`. Use polynomial arithmetic with `[sq_nonneg ‖E d c y‖]`. Introduce `w hεw`. Take `⟨z', hz'L, hz'0, hz'⟩` from `perm_weight hF hU hLst _ w rfl hεw hxL hxL0 hxLw`. Conclude with `hLdom _ z' hz'L hz'0 hz'`.

Set `T0 : Submodule ℂ V` to `S ⊓ LinearMap.ker (CasK ε E - s • (1 : Module.End ℂ V))`. Establish `hT0cas : ∀ v ∈ T0, CasK ε E v = s • v`. Introduce `v hv`. Establish `h` using `(Submodule.mem_inf.mp hv).2`. Rewrite `h` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`.

Conclude with `h`. Establish `hT0st : KStab ε E T0`. Introduce `a b hab v hv`. Use `Submodule.mem_inf.mpr ⟨hSst a b hab v (Submodule.mem_inf.mp hv).1, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`.

Establish `hc` using `congrArg (fun T : Module.End ℂ V => T v) (casK_mul_comm_of_eq_sign hF hab)`. Simplify using `only [Module.End.mul_apply] at hc`. Rewrite using `[hc, hT0cas v hv, map_smul]`. Establish `hxT0 : x ∈ T0`. Use `Submodule.mem_inf.mpr ⟨hxS, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `hcas`. Conclude with `main _ T0 rfl (Submodule.finiteDimensional_of_le inf_le_left) hT0st hT0cas hxT0`.
-/
theorem wtMajor_of (hlow : CompanionTheory.D.DSIC.LowSpan) : CompanionTheory.D.LK.WtMajor := by
  unfold CompanionTheory.D.LK.WtMajor
  intro n ε V _ _ E hF hU hLF μ s x hx0 hxw hcas
  classical
  obtain ⟨S, hSfd, hSst, hxS⟩ := hLF x
  have main : ∀ (N : ℕ) (T : Submodule ℂ V), Module.finrank ℂ T = N → FiniteDimensional ℂ T →
      KStab ε E T → (∀ v ∈ T, CasK ε E v = s • v) → x ∈ T →
      ∃ ν y, y ≠ 0 ∧ KHighest ε E ν y ∧
        s = ↑(PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε)) ∧
        (∀ c d : Fin n, c < d → ε c = ε d → ν d ≤ ν c) ∧
        ∀ w : Equiv.Perm (Fin n), (∀ c, ε (w c) = ε c) → PI.UpqRep.CDom ε (μ ∘ w) ν := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro T hN hTfd hTst hTcas hxT
    haveI : FiniteDimensional ℂ T := hTfd
    have hTne : T ≠ ⊥ := by
      intro h
      rw [h] at hxT
      exact hx0 ((Submodule.mem_bot ℂ).mp hxT)
    obtain ⟨y, hyT, hy0, ν, hyH⟩ := Formalism.REAL.highestWeightExists_holds V n ε E T hTfd hF hU hTst hTne
    obtain ⟨L, hLT, hyL, hLst, -, hLdom, -⟩ := hlow n ε V E ν y T hF hU hy0 hyH hTfd hTst hyT
    haveI : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLT
    obtain ⟨xL, hxL, xp, hxp, hxsplit⟩ := Submodule.exists_add_mem_mem_orthogonal (K := L) x
    have hLpst := kstab_orthogonal hU hLst
    have hsplit : ∀ (A : Module.End ℂ V) (c : ℂ), (∀ v ∈ L, A v ∈ L) → (∀ v ∈ Lᗮ, A v ∈ Lᗮ) →
        A x = c • x → A xL = c • xL := by
      intro A c hAL hAp hAx
      have h1 : A xL - c • xL ∈ L := L.sub_mem (hAL _ hxL) (L.smul_mem _ hxL)
      have h0 : A xL + A xp = c • xL + c • xp := by
        rw [← map_add, ← smul_add, ← hxsplit, hAx]
      have h2 : A xL - c • xL = -(A xp - c • xp) := by
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, add_comm (c • xp)]
        exact h0
      have h3 : A xL - c • xL ∈ Lᗮ := by
        rw [h2]
        exact Lᗮ.neg_mem (Lᗮ.sub_mem (hAp _ hxp) (Lᗮ.smul_mem _ hxp))
      exact sub_eq_zero.mp (inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal h1 h3))
    by_cases hxL0 : xL = 0
    · have hxp' : x ∈ Lᗮ := by rw [hxsplit, hxL0, zero_add]; exact hxp
      have hlt : T ⊓ Lᗮ < T := by
        refine lt_of_le_of_ne inf_le_left fun h => hy0 ?_
        have hy' : y ∈ T ⊓ Lᗮ := by rw [h]; exact hyT
        exact inner_self_eq_zero.mp
          (Submodule.inner_right_of_mem_orthogonal hyL (Submodule.mem_inf.mp hy').2)
      have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
      refine ih _ (hN ▸ hlt') (T ⊓ Lᗮ) rfl (Submodule.finiteDimensional_of_le inf_le_left) ?_ ?_
        (Submodule.mem_inf.mpr ⟨hxT, hxp'⟩)
      · intro a b hab v hv
        exact Submodule.mem_inf.mpr ⟨hTst a b hab v (Submodule.mem_inf.mp hv).1,
          hLpst a b hab v (Submodule.mem_inf.mp hv).2⟩
      · intro v hv
        exact hTcas v (Submodule.mem_inf.mp hv).1
    · have hxLw : IsWeight E μ xL := fun a =>
        hsplit (E a a) (μ a) (fun v hv => hLst a a rfl v hv) (fun v hv => hLpst a a rfl v hv) (hxw a)
      have hform := casK_apply_eq_of_kHighest hF hyH
      rw [hTcas y hyT] at hform
      have hs : s = ↑(PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε)) :=
        smul_left_injective ℂ hy0 hform
      refine ⟨ν, y, hy0, hyH, hs, ?_, ?_⟩
      · intro c d hcd he
        have hid := norm_identity hF hU he hyH.1
        rw [hyH.2 c d hcd he, norm_zero] at hid
        have hy2 : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy0) 2
        nlinarith [sq_nonneg ‖E d c y‖]
      · intro w hεw
        obtain ⟨z', hz'L, hz'0, hz'⟩ := perm_weight hF hU hLst _ w rfl hεw hxL hxL0 hxLw
        exact hLdom _ z' hz'L hz'0 hz'
  let T0 : Submodule ℂ V := S ⊓ LinearMap.ker (CasK ε E - s • (1 : Module.End ℂ V))
  have hT0cas : ∀ v ∈ T0, CasK ε E v = s • v := by
    intro v hv
    have h := (Submodule.mem_inf.mp hv).2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h
  have hT0st : KStab ε E T0 := by
    intro a b hab v hv
    refine Submodule.mem_inf.mpr ⟨hSst a b hab v (Submodule.mem_inf.mp hv).1, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hc := congrArg (fun T : Module.End ℂ V => T v) (casK_mul_comm_of_eq_sign hF hab)
    simp only [Module.End.mul_apply] at hc
    rw [hc, hT0cas v hv, map_smul]
  have hxT0 : x ∈ T0 := by
    refine Submodule.mem_inf.mpr ⟨hxS, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    exact hcas
  exact main _ T0 rfl (Submodule.finiteDimensional_of_le inf_le_left) hT0st hT0cas hxT0

end GlobalTheory.CompanionTheory.KWeightMajor
