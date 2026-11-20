import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

/- English proof (translation)
Establish `: NeZero g` using `⟨hg⟩`. Establish `h` using `Nat.card_le_card_of_injective (Units.val : GL (Fin r) (ZMod g) → Matrix (Fin r) (Fin r) (ZMod g)) Units.val_injective`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Unfold `Matrix`. Rewrite using `[Nat.card_fun, Nat.card_fun, Nat.card_zmod, ← pow_mul]`.

Simplify using `[sq]`.
-/
theorem card_GL_zmod_le (r g : ℕ) (hg : g ≠ 0) : Nat.card (GL (Fin r) (ZMod g)) ≤ g ^ (r ^ 2) := by
  have : NeZero g := ⟨hg⟩
  have h := Nat.card_le_card_of_injective (Units.val : GL (Fin r) (ZMod g) → Matrix (Fin r) (Fin r) (ZMod g))
    Units.val_injective
  refine h.trans (le_of_eq ?_)
  unfold Matrix
  rw [Nat.card_fun, Nat.card_fun, Nat.card_zmod, ← pow_mul]
  simp [sq]

/- English proof (translation)
Establish `hc : Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) = N ^ Module.finrank ℚ E`. Rewrite using `[← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]`. Establish `: Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})` using `Nat.finite_of_card_ne_zero (by rw [hc]; positivity)`. Conclude with `⟨Nat.card_pos, hc ▸ Nat.card_le_card_of_injective _ Units.val_injective⟩`.
-/
theorem card_units_quot_le (E : Type) [Field E] [NumberField E] (N : ℕ) (hN : N ≠ 0) :
    0 < Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ∧
      Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)})ˣ ≤ N ^ Module.finrank ℚ E := by
  have hc : Nat.card (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) = N ^ Module.finrank ℚ E := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  exact ⟨Nat.card_pos, hc ▸ Nat.card_le_card_of_injective _ Units.val_injective⟩

/- English proof (translation)
Establish `hg : ∀ k, P.host.g k ≠ 0` using `fun k => (P.host.g_prime k).ne_zero`. Establish `hg' : ∀ k, (P.host.g k : ℝ) ≠ 0` using `fun k => Nat.cast_ne_zero.2 (hg k)`. Establish `h0` using `h.g 0`. Establish `h1` using `h.g 1`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hle : P.restRowsFiniteGroupCard ≤ (P.host.g 0 * P.host.g 1) ^ (P.R.f * P.R.r ^ 2)`. Unfold `Pre.restRowsFiniteGroupCard`. Rewrite using `[Fin.prod_univ_two, mul_pow, mul_comm P.R.f, pow_mul, pow_mul]`. Conclude with `Nat.mul_le_mul (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 0)) _) (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 1)) _)`. Establish `hpos : (0 : ℝ) < P.restRowsFiniteGroupCard` using `Nat.cast_pos.2 P.restRowsFiniteGroupCard_pos`.

Use `(Real.log_le_log hpos (Nat.cast_le.2 hle)).trans ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0), Real.log_mul (hg' 0) (hg' 1)]`. Use `push_cast`. Conclude with `mul_le_mul_of_nonneg_left (by linarith) (by positivity)`. Introduce `p hp`.

Establish `hp' : p ≠ 0 ∧ Real.log p ≤ L`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hp`. Break down `hp with rfl | rfl` into its components or cases. Conclude with `⟨(P.level_prime _ P.host.pde_level.1).ne_zero, h.p.1⟩`. Conclude with `⟨(P.level_prime _ P.host.pde_level.2).ne_zero, h.p.2⟩`.

Establish `hN : P.host.g 0 * P.host.g 1 * p ≠ 0` using `mul_ne_zero (mul_ne_zero (hg 0) (hg 1)) hp'.1`. Take `⟨hu, hu'⟩` from `card_units_quot_le P.host.E _ hN`. Establish `hE : Module.finrank ℚ P.host.E = 2 * P.R.f`. Rewrite using `[P.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hh : 0 < classNumber P.host.E` using `classNumber_pos _`. Use `⟨by unfold xiOrd; positivity, ?_⟩` and prove the remaining obligations. Unfold `xiOrd`. Generalize the expression as in `Nat.card (𝓞 P.host.E ⧸ Ideal.span {((P.host.g 0 * P.host.g 1 * p : ℕ) : 𝓞 P.host.E)})ˣ = c at hu hu' ⊢`. Establish `hu1 : (0 : ℝ) < c` using `Nat.cast_pos.2 hu`.

Establish `hh1 : (0 : ℝ) < classNumber P.host.E` using `Nat.cast_pos.2 hh`. Establish `h2 : Real.log 2 ≤ 1` using `by linarith [Real.log_two_lt_d9]`. Establish `h3` using `Real.log_le_log hu1 (Nat.cast_le.2 hu')`. Establish `hp0 : (p : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hp'.1`. Rewrite `h3` using `[hE, Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0 * P.host.g 1), Nat.cast_mul (P.host.g 0), Real.log_mul (mul_ne_zero (hg' 0) (hg' 1)) hp0, Real.log_mul (hg' 0) (hg' 1), Nat.cast_mul, Nat.cast_ofNat]`.

Establish `h4 : 2 * (P.R.f : ℝ) * (Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log p) ≤ 2 * P.R.f * (21 * L)` using `mul_le_mul_of_nonneg_left (by linarith [h.len, hp'.2]) (by positivity)`. Rewrite using `[Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by positivity) hu1.ne', Real.log_mul two_ne_zero hh1.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he` using `P.host.two_le_e`. Establish `: 2 ^ 2 ≤ 2 ^ P.R.e` using `Nat.pow_le_pow_right two_pos he`.

Establish `h2` using `P.R.toFrame.two_pow_le_ord`. Unfold `Ranks.f Ranks.n`. Use linear arithmetic over natural numbers and integers. Use `P.R.m_add_three_le_k` as an intermediate fact. Unfold `Ranks.r`.

Use linear arithmetic over natural numbers and integers.
-/
theorem roots_sizes (P : Pre) (L : ℝ) (h : HostSz P.host L) :
    Real.log P.restRowsFiniteGroupCard ≤ P.R.f * (P.R.r : ℝ) ^ 2 * (18 * L + 2) ∧
      (∀ p ∈ [P.host.pde, P.host.pde'], 0 < xiOrd P.host (P.host.g 0 * P.host.g 1 * p) ∧
        Real.log (xiOrd P.host (P.host.g 0 * P.host.g 1 * p)) ≤
          1 + Real.log (classNumber P.host.E) + 2 * P.R.f * (21 * L)) ∧ 8 ≤ P.R.f ∧ 2 * P.R.m ≤ P.R.r := by
  have hg : ∀ k, P.host.g k ≠ 0 := fun k => (P.host.g_prime k).ne_zero
  have hg' : ∀ k, (P.host.g k : ℝ) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hg k)
  have h0 := h.g 0
  have h1 := h.g 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hle : P.restRowsFiniteGroupCard ≤ (P.host.g 0 * P.host.g 1) ^ (P.R.f * P.R.r ^ 2) := by
      unfold Pre.restRowsFiniteGroupCard
      rw [Fin.prod_univ_two, mul_pow, mul_comm P.R.f, pow_mul, pow_mul]
      exact Nat.mul_le_mul (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 0)) _)
        (Nat.pow_le_pow_left (card_GL_zmod_le _ _ (hg 1)) _)
    have hpos : (0 : ℝ) < P.restRowsFiniteGroupCard := Nat.cast_pos.2 P.restRowsFiniteGroupCard_pos
    refine (Real.log_le_log hpos (Nat.cast_le.2 hle)).trans ?_
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0), Real.log_mul (hg' 0) (hg' 1)]
    push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · intro p hp
    have hp' : p ≠ 0 ∧ Real.log p ≤ L := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ⟨(P.level_prime _ P.host.pde_level.1).ne_zero, h.p.1⟩
      · exact ⟨(P.level_prime _ P.host.pde_level.2).ne_zero, h.p.2⟩
    have hN : P.host.g 0 * P.host.g 1 * p ≠ 0 := mul_ne_zero (mul_ne_zero (hg 0) (hg 1)) hp'.1
    obtain ⟨hu, hu'⟩ := card_units_quot_le P.host.E _ hN
    have hE : Module.finrank ℚ P.host.E = 2 * P.R.f := by
      rw [P.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    have hh : 0 < classNumber P.host.E := classNumber_pos _
    refine ⟨by unfold xiOrd; positivity, ?_⟩
    unfold xiOrd
    generalize Nat.card (𝓞 P.host.E ⧸
        Ideal.span {((P.host.g 0 * P.host.g 1 * p : ℕ) : 𝓞 P.host.E)})ˣ = c at hu hu' ⊢
    have hu1 : (0 : ℝ) < c := Nat.cast_pos.2 hu
    have hh1 : (0 : ℝ) < classNumber P.host.E := Nat.cast_pos.2 hh
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h3 := Real.log_le_log hu1 (Nat.cast_le.2 hu')
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp'.1
    rw [hE, Nat.cast_pow, Real.log_pow, Nat.cast_mul (P.host.g 0 * P.host.g 1), Nat.cast_mul (P.host.g 0),
      Real.log_mul (mul_ne_zero (hg' 0) (hg' 1)) hp0, Real.log_mul (hg' 0) (hg' 1), Nat.cast_mul,
      Nat.cast_ofNat] at h3
    have h4 : 2 * (P.R.f : ℝ) * (Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log p) ≤
        2 * P.R.f * (21 * L) :=
      mul_le_mul_of_nonneg_left (by linarith [h.len, hp'.2]) (by positivity)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by positivity) hu1.ne',
      Real.log_mul two_ne_zero hh1.ne']
    linarith
  · have he := P.host.two_le_e
    have : 2 ^ 2 ≤ 2 ^ P.R.e := Nat.pow_le_pow_right two_pos he
    have h2 := P.R.toFrame.two_pow_le_ord
    unfold Ranks.f Ranks.n
    omega
  · have := P.R.m_add_three_le_k
    unfold Ranks.r
    omega

end GlobalTheory.FieldSize
