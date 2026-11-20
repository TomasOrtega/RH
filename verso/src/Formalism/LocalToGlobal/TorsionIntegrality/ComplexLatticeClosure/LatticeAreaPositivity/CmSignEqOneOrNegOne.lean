import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.ThetaTranslationOperatorApply
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Th0TranslateProduct

noncomputable section
open scoped ComplexConjugate

namespace Formalism.L2.Th1.F2

open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions

def ee (L : PeriodPair) (z ω : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * F.herm L z ω + (Real.pi : ℂ) * F.herm L ω ω / 2)

/- English proof (translation)
Establish `h : F.herm L y x = conj (F.herm L x y)`. Unfold `F.herm`. Simplify using `[map_div₀, mul_comm]`. Rewrite using `[h, Complex.sub_conj]`. Unfold `F.altE`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_sub (L : PeriodPair) (x y : ℂ) :
    F.herm L x y - F.herm L y x = 2 * Complex.I * (F.altE L x y : ℂ) := by
  have h : F.herm L y x = conj (F.herm L x y) := by
    unfold F.herm
    simp [map_div₀, mul_comm]
  rw [h, Complex.sub_conj]
  unfold F.altE
  push_cast
  ring

/- English proof (translation)
Unfold `ee`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add]`. Use `congr 1`. Establish `e1 : F.herm L (z + x) y = F.herm L z y + F.herm L x y` using `by unfold F.herm; ring`. Establish `e2 : F.herm L z (x + y) = F.herm L z x + F.herm L z y` using `by unfold F.herm; rw [map_add]; ring`.

Establish `e3 : F.herm L (x + y) (x + y) = F.herm L x x + F.herm L x y + F.herm L y x + F.herm L y y`. Unfold `F.herm`. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, e3]`.

Take the linear combination `((Real.pi : ℂ) / 2) * herm_sub L x y`.
-/
theorem ee_add (L : PeriodPair) (z x y : ℂ) :
    ee L (z + x) y * ee L z x
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (F.altE L x y : ℂ)) * ee L z (x + y) := by
  unfold ee
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have e1 : F.herm L (z + x) y = F.herm L z y + F.herm L x y := by unfold F.herm; ring
  have e2 : F.herm L z (x + y) = F.herm L z x + F.herm L z y := by unfold F.herm; rw [map_add]; ring
  have e3 : F.herm L (x + y) (x + y) = F.herm L x x + F.herm L x y + F.herm L y x + F.herm L y y := by
    unfold F.herm; rw [map_add]; ring
  rw [e1, e2, e3]
  linear_combination ((Real.pi : ℂ) / 2) * herm_sub L x y

/- English proof (translation)
Unfold `ee`. Rewrite using `[← Complex.exp_add]`. Use `Complex.exp_zero using 2` and compare the differences between its conclusion and the goal. Unfold `F.herm`. Rewrite using `[map_neg]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_neg (L : PeriodPair) (z x : ℂ) : ee L (z - x) x * ee L z (-x) = 1 := by
  unfold ee
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 2
  unfold F.herm
  rw [map_neg]
  ring

/- English proof (translation)
Unfold `ee F.herm`. Simplify using the standard rewrite rules.
-/
theorem ee_zero (L : PeriodPair) (z : ℂ) : ee L z 0 = 1 := by
  unfold ee F.herm
  simp

/- English proof (translation)
Unfold `F.altE F.herm`. Rewrite using `[add_mul, add_div, Complex.add_im]`.
-/
theorem altE_add_left (L : PeriodPair) (x y w : ℂ) : F.altE L (x + y) w = F.altE L x w + F.altE L y w := by
  unfold F.altE F.herm
  rw [add_mul, add_div, Complex.add_im]

/- English proof (translation)
Unfold `F.altE F.herm`. Rewrite using `[neg_mul, neg_div, Complex.neg_im]`.
-/
theorem altE_neg_left (L : PeriodPair) (x w : ℂ) : F.altE L (-x) w = -F.altE L x w := by
  unfold F.altE F.herm
  rw [neg_mul, neg_div, Complex.neg_im]

/- English proof (translation)
Unfold `F.thetaZeroCharacter`. Rewrite using `[F.semiCharMul L x y hx hy, altE_add_left]`. Use `push_cast`. Rewrite using `[mul_add, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem th0Char_add (L : PeriodPair) (ω₀ x y : ℂ) (hx : x ∈ L.lattice) (hy : y ∈ L.lattice) :
    F.thetaZeroCharacter L ω₀ (x + y) = F.thetaZeroCharacter L ω₀ x * F.thetaZeroCharacter L ω₀ y
      * Complex.exp ((Real.pi : ℂ) * Complex.I * (F.altE L x y : ℂ)) := by
  unfold F.thetaZeroCharacter
  rw [F.semiCharMul L x y hx hy, altE_add_left]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

/- English proof (translation)
Unfold `F.semiChar`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem semiChar_sq (L : PeriodPair) (x : ℂ) : F.semiChar L x * F.semiChar L x = 1 := by
  unfold F.semiChar
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `F.semiChar`. Establish `h : (-x / 2 ∈ L.lattice) ↔ (x / 2 ∈ L.lattice)` using `by rw [neg_div]; exact neg_mem_iff`. Distinguish the cases in `hx : x / 2 ∈ L.lattice`. Rewrite using `[if_pos hx, if_pos (h.mpr hx)]`. Rewrite using `[if_neg hx, if_neg (fun h' => hx (h.mp h'))]`.
-/
theorem semiChar_neg (L : PeriodPair) (x : ℂ) : F.semiChar L (-x) = F.semiChar L x := by
  unfold F.semiChar
  have h : (-x / 2 ∈ L.lattice) ↔ (x / 2 ∈ L.lattice) := by rw [neg_div]; exact neg_mem_iff
  by_cases hx : x / 2 ∈ L.lattice
  · rw [if_pos hx, if_pos (h.mpr hx)]
  · rw [if_neg hx, if_neg (fun h' => hx (h.mp h'))]

/- English proof (translation)
Unfold `F.thetaZeroCharacter`. Rewrite using `[semiChar_neg, altE_neg_left]`. Establish `h : Complex.exp ((Real.pi : ℂ) * Complex.I * ((-F.altE L x ω₀ : ℝ) : ℂ)) * Complex.exp ((Real.pi : ℂ) * Complex.I * (F.altE L x ω₀ : ℂ)) = 1`. Rewrite using `[← Complex.exp_add]`. Use `Complex.exp_zero using 2` and compare the differences between its conclusion and the goal.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation.
-/
theorem th0Char_neg (L : PeriodPair) (ω₀ x : ℂ) : F.thetaZeroCharacter L ω₀ (-x) * F.thetaZeroCharacter L ω₀ x = 1 := by
  unfold F.thetaZeroCharacter
  rw [semiChar_neg, altE_neg_left]
  have h : Complex.exp ((Real.pi : ℂ) * Complex.I * ((-F.altE L x ω₀ : ℝ) : ℂ))
      * Complex.exp ((Real.pi : ℂ) * Complex.I * (F.altE L x ω₀ : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast
    ring
  calc _ = (F.semiChar L x * F.semiChar L x) * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((-F.altE L x ω₀ : ℝ) : ℂ))
      * Complex.exp ((Real.pi : ℂ) * Complex.I * (F.altE L x ω₀ : ℂ))) := by ring
    _ = 1 := by rw [semiChar_sq, h, one_mul]

/- English proof (translation)
Unfold `F.thetaZeroCharacter F.semiChar F.altE F.herm`. Simplify using the standard rewrite rules.
-/
theorem th0Char_zero (L : PeriodPair) (ω₀ : ℂ) : F.thetaZeroCharacter L ω₀ 0 = 1 := by
  unfold F.thetaZeroCharacter F.semiChar F.altE F.herm
  simp

def eqGroup (L : PeriodPair) (ω₀ : ℂ) (G : ℂ → ℂ) : AddSubgroup ℂ where
  carrier := {ω | ω ∈ L.lattice ∧ ∀ z, G (z + ω) = F.thetaZeroCharacter L ω₀ ω * ee L z ω * G z}
  zero_mem' := ⟨zero_mem _, fun z => by rw [th0Char_zero, ee_zero, add_zero, one_mul, one_mul]⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨add_mem hx hy, fun z => ?_⟩
    rw [← add_assoc, hy' (z + x), hx' z, th0Char_add L ω₀ x y hx hy]
    linear_combination (F.thetaZeroCharacter L ω₀ x * F.thetaZeroCharacter L ω₀ y * G z) * ee_add L z x y
  neg_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨neg_mem hx, fun z => ?_⟩
    have h := hx' (z - x)
    rw [sub_add_cancel] at h
    rw [h, ← sub_eq_add_neg]
    linear_combination (-(F.thetaZeroCharacter L ω₀ (-x) * F.thetaZeroCharacter L ω₀ x) * G (z - x)) * ee_neg L z x
      - G (z - x) * th0Char_neg L ω₀ x

/- English proof (translation)
Establish `hle : L.lattice ≤ AddSubgroup.toIntSubmodule (eqGroup L ω₀ G)`. Unfold `PeriodPair.lattice`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `w (rfl | rfl)`. Conclude with `⟨L.ω₁_mem_lattice, h1⟩`.

Conclude with `⟨L.ω₂_mem_lattice, h2⟩`. Introduce `ω hω`. Conclude with `(hle hω).2`.
-/
theorem eq_all (L : PeriodPair) (ω₀ : ℂ) (G : ℂ → ℂ)
    (h1 : ∀ z, G (z + L.ω₁) = F.thetaZeroCharacter L ω₀ L.ω₁ * ee L z L.ω₁ * G z)
    (h2 : ∀ z, G (z + L.ω₂) = F.thetaZeroCharacter L ω₀ L.ω₂ * ee L z L.ω₂ * G z) :
    ∀ ω ∈ L.lattice, ∀ z, G (z + ω) = F.thetaZeroCharacter L ω₀ ω * ee L z ω * G z := by
  have hle : L.lattice ≤ AddSubgroup.toIntSubmodule (eqGroup L ω₀ G) := by
    unfold PeriodPair.lattice
    rw [Submodule.span_le]
    rintro w (rfl | rfl)
    · exact ⟨L.ω₁_mem_lattice, h1⟩
    · exact ⟨L.ω₂_mem_lattice, h2⟩
  intro ω hω
  exact (hle hω).2

/- English proof (translation)
Rewrite using `[← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_pi_int' (m : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Unfold `F.altE F.herm`. Rewrite using `[Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_im]`.
-/
theorem altE_self (L : PeriodPair) (x : ℂ) : F.altE L x x = 0 := by
  unfold F.altE F.herm
  rw [Complex.mul_conj, ← Complex.ofReal_div, Complex.ofReal_im]

/- English proof (translation)
Establish `h` using `herm_sub L x y`. Establish `h'` using `herm_sub L y x`. Establish `: (2 * Complex.I) * ((F.altE L y x : ℂ) + (F.altE L x y : ℂ)) = 0`. Take the linear combination `-h - h'`. Establish `h2 : (F.altE L y x : ℂ) + (F.altE L x y : ℂ) = 0`.

Break down `mul_eq_zero.mp this with h3 | h3` into its components or cases. It suffices to derive a contradiction. Simplify using `at h3`. Conclude with `h3`. Establish `h3 : F.altE L y x + F.altE L x y = 0` using `by exact_mod_cast h2`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem altE_swap (L : PeriodPair) (x y : ℂ) : F.altE L y x = -F.altE L x y := by
  have h := herm_sub L x y
  have h' := herm_sub L y x
  have : (2 * Complex.I) * ((F.altE L y x : ℂ) + (F.altE L x y : ℂ)) = 0 := by
    linear_combination -h - h'
  have h2 : (F.altE L y x : ℂ) + (F.altE L x y : ℂ) = 0 := by
    rcases mul_eq_zero.mp this with h3 | h3
    · exfalso; simp at h3
    · exact h3
  have h3 : F.altE L y x + F.altE L x y = 0 := by exact_mod_cast h2
  linarith

/- English proof (translation)
Unfold `F.altE F.herm`. Simplify using `only [map_add, map_mul, map_intCast, Complex.div_ofReal_im, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem altE_right (L : PeriodPair) (w x y : ℂ) (m n : ℤ) :
    F.altE L w ((m : ℂ) * x + (n : ℂ) * y) = m * F.altE L w x + n * F.altE L w y := by
  unfold F.altE F.herm
  simp only [map_add, map_mul, map_intCast, Complex.div_ofReal_im, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
    Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  ring

/- English proof (translation)
Rewrite using `[neg_one_zpow_eq_ite]`. Use `split_ifs`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`.
-/
theorem zpow_pm (n : ℤ) : (-1 : ℂ) ^ n = 1 ∨ (-1 : ℂ) ^ n = -1 := by
  rw [neg_one_zpow_eq_ite]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/- English proof (translation)
Rewrite using `[zpow_neg]`. Apply the tactic sequence `rcases zpow_pm n with h | h <;> rw [h] <;> norm_num`.
-/
theorem neg_one_zpow_neg' (n : ℤ) : (-1 : ℂ) ^ (-n) = (-1 : ℂ) ^ n := by
  rw [zpow_neg]
  rcases zpow_pm n with h | h <;> rw [h] <;> norm_num

/- English proof (translation)
Establish `hb` using `F.altEBasis L`. Establish `s1 : F.semiChar L L.ω₁ = -1`. Unfold `F.semiChar`. Rewrite using `[if_neg L.ω₁_div_two_notMem_lattice]`. Establish `s2 : F.semiChar L L.ω₂ = -1`.

Unfold `F.semiChar`. Rewrite using `[if_neg L.ω₂_div_two_notMem_lattice]`. Unfold `F.thetaZeroCharacter`. Rewrite using `[s1, s2, altE_right, altE_right, altE_self, altE_self, altE_swap L L.ω₁ L.ω₂, hb]`. Use `split_ifs`.

Prove the components needed by the constructor for the conclusion. Establish `: ((m : ℝ) * 0 + (n : ℝ) * (-1)) = ((-n : ℤ) : ℝ)` using `by push_cast; ring`. Rewrite using `[this, exp_pi_int', neg_one_zpow_neg']`. Expand and normalize the polynomial expressions, which then agree. Establish `: ((m : ℝ) * (-(-1)) + (n : ℝ) * 0) = ((m : ℤ) : ℝ)` using `by ring`.

Rewrite using `[this, exp_pi_int']`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Establish `: ((m : ℝ) * 0 + (n : ℝ) * 1) = ((n : ℤ) : ℝ)` using `by ring`. Rewrite using `[this, exp_pi_int']`.

Expand and normalize the polynomial expressions, which then agree. Establish `: ((m : ℝ) * (-1) + (n : ℝ) * 0) = ((-m : ℤ) : ℝ)` using `by push_cast; ring`. Rewrite using `[this, exp_pi_int', neg_one_zpow_neg']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem char_basis (L : PeriodPair) (m n : ℤ) :
    F.thetaZeroCharacter L ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) L.ω₁ = -(-1 : ℂ) ^ n ∧
    F.thetaZeroCharacter L ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) L.ω₂ = -(-1 : ℂ) ^ m := by
  have hb := F.altEBasis L
  have s1 : F.semiChar L L.ω₁ = -1 := by
    unfold F.semiChar; rw [if_neg L.ω₁_div_two_notMem_lattice]
  have s2 : F.semiChar L L.ω₂ = -1 := by
    unfold F.semiChar; rw [if_neg L.ω₂_div_two_notMem_lattice]
  unfold F.thetaZeroCharacter
  rw [s1, s2, altE_right, altE_right, altE_self, altE_self, altE_swap L L.ω₁ L.ω₂, hb]
  split_ifs
  · constructor
    · have : ((m : ℝ) * 0 + (n : ℝ) * (-1)) = ((-n : ℤ) : ℝ) := by push_cast; ring
      rw [this, exp_pi_int', neg_one_zpow_neg']; ring
    · have : ((m : ℝ) * (-(-1)) + (n : ℝ) * 0) = ((m : ℤ) : ℝ) := by ring
      rw [this, exp_pi_int']; ring
  · constructor
    · have : ((m : ℝ) * 0 + (n : ℝ) * 1) = ((n : ℤ) : ℝ) := by ring
      rw [this, exp_pi_int']; ring
    · have : ((m : ℝ) * (-1) + (n : ℝ) * 0) = ((-m : ℤ) : ℝ) := by push_cast; ring
      rw [this, exp_pi_int', neg_one_zpow_neg']; ring

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n : ℤ, -(-1 : ℂ) ^ n = a := by`. Break down `ha with rfl | rfl` into its components or cases. Conclude with `⟨1, by norm_num⟩`. Conclude with `⟨0, by norm_num⟩`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℤ, -(-1 : ℂ) ^ m = b := by`.

Break down `hb with rfl | rfl` into its components or cases. Conclude with `⟨1, by norm_num⟩`. Conclude with `⟨0, by norm_num⟩`. Use `⟨(m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂, PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(char_basis L m n).1, hn]`.

Rewrite using `[(char_basis L m n).2, hm]`.
-/
theorem exists_char (L : PeriodPair) (a b : ℂ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    ∃ ω₀ ∈ L.lattice, F.thetaZeroCharacter L ω₀ L.ω₁ = a ∧ F.thetaZeroCharacter L ω₀ L.ω₂ = b := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, -(-1 : ℂ) ^ n = a := by
    rcases ha with rfl | rfl
    · exact ⟨1, by norm_num⟩
    · exact ⟨0, by norm_num⟩
  obtain ⟨m, hm⟩ : ∃ m : ℤ, -(-1 : ℂ) ^ m = b := by
    rcases hb with rfl | rfl
    · exact ⟨1, by norm_num⟩
    · exact ⟨0, by norm_num⟩
  refine ⟨(m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂, PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩, ?_, ?_⟩
  · rw [(char_basis L m n).1, hn]
  · rw [(char_basis L m n).2, hm]

/- English proof (translation)
The claim follows from `zpow_pm _`.
-/
theorem cm_sign_eq_one_or_neg_one (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : al1 d Λ x = 1 ∨ al1 d Λ x = -1 :=
  zpow_pm _

/- English proof (translation)
Establish `h` using `hG.2.1 x hx z`. Rewrite `h` using `[thetaTranslationOperator_apply]`. Unfold `F.opU at h`. Establish `hsq : al1 d L.lattice.toAddSubgroup x * al1 d L.lattice.toAddSubgroup x = 1`. Apply the tactic sequence `rcases cm_sign_eq_one_or_neg_one d L.lattice.toAddSubgroup x with h | h <;> rw [h] <;> norm_num`.

Establish `hexp : ee L z x * Complex.exp (-(Real.pi : ℂ) * F.herm L z x - (Real.pi : ℂ) * F.herm L x x / 2) = 1`. Unfold `ee`. Rewrite using `[← Complex.exp_add]`. Use `Complex.exp_zero using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← h]`. Take the linear combination `(-(al1 d L.lattice.toAddSubgroup x * al1 d L.lattice.toAddSubgroup x) * G (z + x)) * hexp - G (z + x) * hsq`.
-/
theorem fe_of_isTheta0 (d : ℕ) (L : PeriodPair) (G : ℂ → ℂ) (hG : IsTheta0 d L.lattice.toAddSubgroup G) (x : ℂ)
    (hx : x ∈ L.lattice) (z : ℂ) : G (z + x) = al1 d L.lattice.toAddSubgroup x * ee L z x * G z := by
  have h := hG.2.1 x hx z
  rw [thetaTranslationOperator_apply] at h
  unfold F.opU at h
  have hsq : al1 d L.lattice.toAddSubgroup x * al1 d L.lattice.toAddSubgroup x = 1 := by
    rcases cm_sign_eq_one_or_neg_one d L.lattice.toAddSubgroup x with h | h <;> rw [h] <;> norm_num
  have hexp : ee L z x * Complex.exp (-(Real.pi : ℂ) * F.herm L z x - (Real.pi : ℂ) * F.herm L x x / 2) = 1 := by
    unfold ee
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  rw [← h]
  linear_combination (-(al1 d L.lattice.toAddSubgroup x * al1 d L.lattice.toAddSubgroup x) * G (z + x)) * hexp
    - G (z + x) * hsq

/- English proof (translation)
Take `⟨ω₀, h0, c1, c2⟩` from `exists_char L _ _ (cm_sign_eq_one_or_neg_one d L.lattice.toAddSubgroup L.ω₁) (cm_sign_eq_one_or_neg_one d L.lattice.toAddSubgroup L.ω₂)`. Use `⟨ω₀, h0, fun G hG => ?_⟩` and prove the remaining obligations. Establish `hall` using `eq_all L ω₀ G (fun z => by rw [c1]; exact fe_of_isTheta0 d L G hG _ L.ω₁_mem_lattice z) (fun z => by rw [c2]; exact fe_of_isTheta0 d L G hG _ L.ω₂_mem_lattice z)`. Establish `hhalf : ω₀ / 2 ∉ L.lattice`. Introduce `hh`.

Establish `hline` using `F.thetaLine L G hG.1 (fun ω hω z => by`. Take `⟨k, hk⟩` from `F.altEInt L ω (ω₀ / 2) hω hh`. Establish `hE : F.altE L ω ω₀ = ((2 * k : ℤ) : ℝ)`. Establish `: ω₀ = ((2 : ℤ) : ℂ) * (ω₀ / 2) + ((0 : ℤ) : ℂ) * 0` using `by push_cast; ring`. Rewrite using `[this, altE_right, hk]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : F.thetaZeroCharacter L ω₀ ω = F.semiChar L ω`. Unfold `F.thetaZeroCharacter`. Rewrite using `[hE, exp_pi_int', zpow_mul]`.

Evaluate the numerical expressions. Unfold `F.opU`. Rewrite using `[hall ω hω z, hc]`. Establish `hexp : ee L z ω * Complex.exp (-(Real.pi : ℂ) * F.herm L z ω - (Real.pi : ℂ) * F.herm L ω ω / 2) = 1`. Unfold `ee`.

Rewrite using `[← Complex.exp_add]`. Use `Complex.exp_zero using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(F.semiChar L ω * F.semiChar L ω * G z) * hexp + G z * semiChar_sq L ω)`. Take `⟨c, hc⟩` from `hline`.

Establish `h1` using `hG.2.2`. Rewrite `h1` using `[hc 0, ((F.sgStarBasic L).2.2.1 0).mpr (zero_mem _), mul_zero]`. Conclude with `zero_ne_one h1`. Use `⟨hhalf, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`.

Use `F.th0Line L ω₀ G h0 hhalf hG.1 hall z` as an intermediate fact. Rewrite using `[this, hG.2.2, one_mul]`.
-/
theorem theta0_eq (d : ℕ) (L : PeriodPair) :
    ∃ ω₀ ∈ L.lattice, ∀ G, IsTheta0 d L.lattice.toAddSubgroup G → ω₀ / 2 ∉ L.lattice ∧ G = F.th0 L (ω₀ / 2) := by
  obtain ⟨ω₀, h0, c1, c2⟩ := exists_char L _ _ (cm_sign_eq_one_or_neg_one d L.lattice.toAddSubgroup L.ω₁) (cm_sign_eq_one_or_neg_one d L.lattice.toAddSubgroup L.ω₂)
  refine ⟨ω₀, h0, fun G hG => ?_⟩
  have hall := eq_all L ω₀ G (fun z => by rw [c1]; exact fe_of_isTheta0 d L G hG _ L.ω₁_mem_lattice z)
    (fun z => by rw [c2]; exact fe_of_isTheta0 d L G hG _ L.ω₂_mem_lattice z)
  have hhalf : ω₀ / 2 ∉ L.lattice := by
    intro hh
    have hline := F.thetaLine L G hG.1 (fun ω hω z => by
      obtain ⟨k, hk⟩ := F.altEInt L ω (ω₀ / 2) hω hh
      have hE : F.altE L ω ω₀ = ((2 * k : ℤ) : ℝ) := by
        have : ω₀ = ((2 : ℤ) : ℂ) * (ω₀ / 2) + ((0 : ℤ) : ℂ) * 0 := by push_cast; ring
        rw [this, altE_right, hk]; push_cast; ring
      have hc : F.thetaZeroCharacter L ω₀ ω = F.semiChar L ω := by
        unfold F.thetaZeroCharacter
        rw [hE, exp_pi_int', zpow_mul]
        norm_num
      unfold F.opU
      rw [hall ω hω z, hc]
      have hexp : ee L z ω * Complex.exp (-(Real.pi : ℂ) * F.herm L z ω - (Real.pi : ℂ) * F.herm L ω ω / 2) = 1 := by
        unfold ee
        rw [← Complex.exp_add]
        convert Complex.exp_zero using 2
        ring
      linear_combination (F.semiChar L ω * F.semiChar L ω * G z) * hexp + G z * semiChar_sq L ω)
    obtain ⟨c, hc⟩ := hline
    have h1 := hG.2.2
    rw [hc 0, ((F.sgStarBasic L).2.2.1 0).mpr (zero_mem _), mul_zero] at h1
    exact zero_ne_one h1
  refine ⟨hhalf, ?_⟩
  funext z
  have := F.th0Line L ω₀ G h0 hhalf hG.1 hall z
  rw [this, hG.2.2, one_mul]

/- English proof (translation)
Introduce and unpack `d Λ G G' ⟨L, rfl⟩ hG hG'`. Take `⟨ω₀, -, h⟩` from `theta0_eq d L`. Rewrite using `[(h G hG).2, (h G' hG').2]`.
-/
theorem theta_zero_unique_holds : ThetaZeroUniqueness := by
  rintro d Λ G G' ⟨L, rfl⟩ hG hG'
  obtain ⟨ω₀, -, h⟩ := theta0_eq d L
  rw [(h G hG).2, (h G' hG').2]

end Formalism.L2.Th1.F2
