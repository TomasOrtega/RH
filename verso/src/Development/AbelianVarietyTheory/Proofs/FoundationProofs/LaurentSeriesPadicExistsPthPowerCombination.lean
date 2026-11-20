import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesEqSumSingleMulPowStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.K5.LauZ

variable (p : ℕ) [hp : Fact p.Prime]

def red : Lau p →+* LaurentSeries (ZMod p) where
  toFun f := f.map (PadicInt.toZMod (p := p)).toNonUnitalRingHom
  map_one' := by
    ext n
    show PadicInt.toZMod ((1 : Lau p).coeff n) = (1 : LaurentSeries (ZMod p)).coeff n
    rw [HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> simp
  map_mul' x y := HahnSeries.map_mul _
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem red_coeff (f : Lau p) (n : ℤ) : (red p f).coeff n = PadicInt.toZMod (f.coeff n) := rfl

def lift (F : LaurentSeries (ZMod p)) : Lau p :=
  ⟨fun n => ((F.coeff n).val : ℤ_[p]), F.isPWO_support'.mono fun n hn => by
    simp only [Function.mem_support] at hn ⊢
    intro h; apply hn; rw [h]; simp⟩

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[red_coeff]`. Use `show PadicInt.toZMod (((F.coeff n).val : ℕ) : ℤ_[p]) = F.coeff n`. Rewrite using `[map_natCast, ZMod.natCast_zmod_val]`.
-/
theorem red_lift (F : LaurentSeries (ZMod p)) : red p (lift p F) = F := by
  ext n
  rw [red_coeff]
  show PadicInt.toZMod (((F.coeff n).val : ℕ) : ℤ_[p]) = F.coeff n
  rw [map_natCast, ZMod.natCast_zmod_val]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[red_coeff]`. Distinguish the cases in `h : n = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[HahnSeries.coeff_single_of_ne h]`.
-/
theorem red_single (a : ℤ) : red p (HahnSeries.single a (1 : ℤ_[p])) = HahnSeries.single a (1 : ZMod p) := by
  ext n
  rw [red_coeff]
  by_cases h : n = a
  · subst h; simp
  · simp [HahnSeries.coeff_single_of_ne h]

/- English proof (translation)
Take `⟨G, hG⟩` from `GlobalTheory.T.laurentSeries_eq_sum_single_mul_pow_prime p (red p f)`. Use `set S : Lau p := ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * lift p (G j) ^ p`. Establish `hS : red p S = red p f`. Rewrite using `[hG]`. Simplify using `only [S, map_sum, map_mul, map_pow, red_single, red_lift]`.

Establish `h0 : (f - S).map (PadicInt.toZMod (p` using `p)).toNonUnitalRingHom = 0 := by show red p (f - S) = 0`. Rewrite using `[map_sub, hS, sub_self]`. Take `⟨h, hh⟩` from `(GlobalTheory.K5.Basic.dvd_iff_map p (f - S)).2 h0`. Conclude with `⟨fun j => lift p (G j), h, by rw [← hh, add_sub_cancel]⟩`.
-/
theorem exists_pow_comb (f : Lau p) : ∃ (g : Fin p → Lau p) (h : Lau p),
    f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * g j ^ p + (p : Lau p) * h := by
  obtain ⟨G, hG⟩ := GlobalTheory.T.laurentSeries_eq_sum_single_mul_pow_prime p (red p f)
  set S : Lau p := ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * lift p (G j) ^ p
  have hS : red p S = red p f := by
    rw [hG]
    simp only [S, map_sum, map_mul, map_pow, red_single, red_lift]
  have h0 : (f - S).map (PadicInt.toZMod (p := p)).toNonUnitalRingHom = 0 := by
    show red p (f - S) = 0
    rw [map_sub, hS, sub_self]
  obtain ⟨h, hh⟩ := (GlobalTheory.K5.Basic.dvd_iff_map p (f - S)).2 h0
  exact ⟨fun j => lift p (G j), h, by rw [← hh, add_sub_cancel]⟩

end GlobalTheory.K5.LauZ

end
