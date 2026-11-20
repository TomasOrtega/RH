import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormPowSubPowLe
open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

/- English proof (translation)
Establish `h1 : ‖(n : ℚ_[l])‖ = 1`. Break down `(Padic.norm_int_le_one (p := l) n).eq_or_lt with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd (Padic.norm_intCast_lt_one_iff.1 h1) h`. Establish `h2 : (n : Qbar l) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l])` using `by simp`.

Rewrite using `[h2, norm_algebraMap', h1]`.
-/
private theorem norm_int_eq_one (l : ℕ) [Fact l.Prime] (n : ℤ) (h : ¬ (l : ℤ) ∣ n) : ‖(n : Qbar l)‖ = 1 := by
  have h1 : ‖(n : ℚ_[l])‖ = 1 := by
    rcases (Padic.norm_int_le_one (p := l) n).eq_or_lt with h1 | h1
    · exact h1
    · exact absurd (Padic.norm_intCast_lt_one_iff.1 h1) h
  have h2 : (n : Qbar l) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l]) := by simp
  rw [h2, norm_algebraMap', h1]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qi18.norm_pow_sub_pow_le x y hx hy e`.
-/
private theorem norm_pow_sub_pow_le {K : Type*} [NormedField K] [IsUltrametricDist K] (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (e : ℕ) : ‖x ^ e - y ^ e‖ ≤ ‖x - y‖ :=
  _root_.UpperTheory.Reformulated.B.Qi18.norm_pow_sub_pow_le x y hx hy e

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Rewrite using `[MulChar.map_zero]`. Simplify using the standard rewrite rules. Establish `h1 : x ^ (l - 1) = 1` using `ZMod.pow_card_sub_one_eq_one hx`.

Establish `h2 : ‖φ x‖ ^ (l - 1) = 1` using `by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]`. Establish `h3 : l - 1 ≠ 0` using `by have := (Fact.out : l.Prime).two_le; omega`. Conclude with `((pow_eq_one_iff_of_nonneg (norm_nonneg _) h3).1 h2).le`.
-/
private theorem norm_char_le_one (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (x : ZMod l) :
    ‖φ x‖ ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    rw [MulChar.map_zero]; simp
  · have h1 : x ^ (l - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
    have h2 : ‖φ x‖ ^ (l - 1) = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
    have h3 : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) h3).1 h2).le

/- English proof (translation)
Introduce `l _ r e φ y a n hr ha hn hy`. Establish `hp : l.Prime` using `Fact.out`. Use `haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩`. Establish `hd : ((l ^ r : ℕ) : ℤ) ∣ (y.val : ℤ) * a - n`. Rewrite using `[← ZMod.intCast_eq_intCast_iff_dvd_sub]`.

Use `push_cast`. Rewrite using `[ZMod.natCast_zmod_val, hy]`. Establish `hl : (l : ℤ) ∣ (y.val : ℤ) * a - n`. Use `dvd_trans ?_ hd` and prove the remaining obligations. Use `push_cast`.

Conclude with `dvd_pow_self _ (by omega)`. Establish `hyv : ¬ l ∣ y.val`. Introduce `h`. Apply `hn` to reduce the goal to its premises. Establish `h1 : (l : ℤ) ∣ (y.val : ℤ) * a` using `(Int.natCast_dvd_natCast.2 h).mul_right _`.

Establish `h2` using `dvd_sub h1 hl`. Simplify using `using h2`. Use `⟨hyv, ?_⟩` and prove the remaining obligations. Establish `hmod : ((n : ℤ) : ZMod l) = (y.val : ZMod l) * (a : ZMod l)`. Use `(ZMod.intCast_eq_intCast_iff_dvd_sub n ((y.val : ℤ) * a) l).2 hl` as an intermediate fact.

Rewrite using `[this]`. Use `push_cast`. Both sides reduce to the same expression. Establish `ha0 : (a : ZMod l) ≠ 0`. Rewrite using `[Ne, ZMod.natCast_eq_zero_iff]` and apply the resulting hypothesis.

Establish `hφa : φ (a : ZMod l) * φ⁻¹ (a : ZMod l) = 1`. Rewrite using `[← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply (Ne.isUnit ha0)]`. Establish `hφ : φ (n : ZMod l) * φ⁻¹ (a : ZMod l) = φ (y.val : ZMod l)`. Rewrite using `[hmod, map_mul, mul_assoc, hφa, mul_one]`. Establish `hna : ‖(a : Qbar l)‖ = 1`.

Use `norm_int_eq_one l (a : ℤ) (by rwa [Int.natCast_dvd_natCast])` as an intermediate fact. Simplify using `using this`. Establish `haK : (a : Qbar l) ≠ 0`. Introduce `h`. Rewrite `hna` using `[h, norm_zero]`.

Conclude with `zero_ne_one hna`. Rewrite using `[hφ, ← mul_sub, norm_mul]`. Use `(mul_le_of_le_one_left (norm_nonneg _) (norm_char_le_one l φ _)).trans ?_` and prove the remaining obligations. Use `(norm_pow_sub_pow_le _ _ (IsUltrametricDist.norm_natCast_le_one _ _) ?_ e).trans ?_` and prove the remaining obligations. Rewrite using `[norm_div, hna, div_one]`.

Conclude with `IsUltrametricDist.norm_intCast_le_one _ _`. Take `⟨c, hc⟩` from `hd`. Establish `hc' : (y.val : Qbar l) * a - n = (l : Qbar l) ^ r * c`. Conclude with `congrArg (Int.cast : ℤ → Qbar l) hc` after adjusting the coercions. Establish `h : (y.val : Qbar l) - (n : Qbar l) / a = (l : Qbar l) ^ r * c / a`.

Rewrite using `[← hc']`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h, norm_div, hna, div_one, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)`.
-/
theorem UpperTheory.norm_character_pow_difference_estimate :
    ∀ (l : ℕ) [Fact l.Prime] (r e : ℕ) (φ : DirichletCharacter (Qbar l) l) (y : ZMod (l ^ r)) (a : ℕ) (n : ℤ), 1 ≤ r → ¬ l ∣ a → ¬ (l : ℤ) ∣ n →
      y * (a : ZMod (l ^ r)) = (n : ZMod (l ^ r)) →
      ¬ l ∣ y.val ∧ ‖φ (y.val : ZMod l) * (y.val : Qbar l) ^ e - φ (n : ZMod l) * φ⁻¹ (a : ZMod l) * ((n : Qbar l) / a) ^ e‖ ≤ ‖(l : Qbar l) ^ r‖ := by
  intro l _ r e φ y a n hr ha hn hy
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hd : ((l ^ r : ℕ) : ℤ) ∣ (y.val : ℤ) * a - n := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [ZMod.natCast_zmod_val, hy]
  have hl : (l : ℤ) ∣ (y.val : ℤ) * a - n := by
    refine dvd_trans ?_ hd
    push_cast
    exact dvd_pow_self _ (by omega)
  have hyv : ¬ l ∣ y.val := by
    intro h
    apply hn
    have h1 : (l : ℤ) ∣ (y.val : ℤ) * a := (Int.natCast_dvd_natCast.2 h).mul_right _
    have h2 := dvd_sub h1 hl
    simpa using h2
  refine ⟨hyv, ?_⟩
  have hmod : ((n : ℤ) : ZMod l) = (y.val : ZMod l) * (a : ZMod l) := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub n ((y.val : ℤ) * a) l).2 hl
    rw [this]; push_cast; rfl
  have ha0 : (a : ZMod l) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  have hφa : φ (a : ZMod l) * φ⁻¹ (a : ZMod l) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply (Ne.isUnit ha0)]
  have hφ : φ (n : ZMod l) * φ⁻¹ (a : ZMod l) = φ (y.val : ZMod l) := by
    rw [hmod, map_mul, mul_assoc, hφa, mul_one]
  have hna : ‖(a : Qbar l)‖ = 1 := by
    have := norm_int_eq_one l (a : ℤ) (by rwa [Int.natCast_dvd_natCast])
    simpa using this
  have haK : (a : Qbar l) ≠ 0 := by
    intro h; rw [h, norm_zero] at hna; exact zero_ne_one hna
  rw [hφ, ← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (norm_char_le_one l φ _)).trans ?_
  refine (norm_pow_sub_pow_le _ _ (IsUltrametricDist.norm_natCast_le_one _ _) ?_ e).trans ?_
  · rw [norm_div, hna, div_one]
    exact IsUltrametricDist.norm_intCast_le_one _ _
  · obtain ⟨c, hc⟩ := hd
    have hc' : (y.val : Qbar l) * a - n = (l : Qbar l) ^ r * c := by
      exact_mod_cast congrArg (Int.cast : ℤ → Qbar l) hc
    have h : (y.val : Qbar l) - (n : Qbar l) / a = (l : Qbar l) ^ r * c / a := by
      rw [← hc']; field_simp
    rw [h, norm_div, hna, div_one, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)
