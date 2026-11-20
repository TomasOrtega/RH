import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of
import Formalism.LFunctionBounds.LFunctionBoundsProofs.LPartialSum
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

def cS (U : ℕ) : ℂ := ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ)

def cT (U : ℕ) : ℂ := ∑ b ∈ Ioc 0 U, χ (b : ZMod q) * (Real.log b : ℂ) / (b : ℂ)

def cF (N : ℕ) : ℂ := ∑ n ∈ Ioc 0 N, (∑ d ∈ n.divisors, χ (d : ZMod q)) / (n : ℂ)

def hH (k : ℕ) : ℝ := ∑ a ∈ Ioc 0 k, ((a : ℝ))⁻¹

/- English proof (translation)
Establish `hcond : ∀ (n d : ℕ), n ∈ Finset.Ioc 0 N ∧ d ∈ n.divisors ↔ n ∈ (Finset.Ioc 0 N).filter (d ∣ ·) ∧ d ∈ Finset.Ioc 0 N`. Introduce `n d`. Simplify using `only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hn0, hnN⟩, hdn, -⟩`.

Establish `h1` using `Nat.le_of_dvd hn0 hdn`. Establish `h2` using `Nat.pos_of_dvd_of_pos hdn hn0`. Conclude with `⟨⟨⟨hn0, hnN⟩, hdn⟩, h2, by omega⟩`. Introduce and unpack `⟨⟨⟨hn0, hnN⟩, hdn⟩, -, -⟩`. Conclude with `⟨⟨hn0, hnN⟩, hdn, by omega⟩`.

Unfold `cF hH`. Simplify using `only [Finset.sum_div]`. Rewrite using `[Finset.sum_comm' hcond]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hd0 : 0 < d` using `(Finset.mem_Ioc.mp hd).1`.

Establish `himg : (Finset.Ioc 0 N).filter (d ∣ ·) = (Finset.Ioc 0 (N / d)).image (fun a => d * a)`. Use extensionality with `n`. Simplify using `only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, ⟨a, rfl⟩⟩`.

Use `⟨a, ⟨?_, ?_⟩, rfl⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos a with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `at h1`. Conclude with `h`.

Conclude with `(Nat.le_div_iff_mul_le hd0).mpr (by rw [mul_comm]; exact h2)`. Introduce and unpack `⟨a, ⟨h1, h2⟩, rfl⟩`. Use `⟨⟨Nat.mul_pos hd0 h1, ?_⟩, dvd_mul_right d a⟩` and prove the remaining obligations. Establish `h3` using `(Nat.le_div_iff_mul_le hd0).mp h2`. Rewrite using `[mul_comm]`.

Conclude with `h3`. Rewrite using `[himg, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd0 h)]`. Use `push_cast`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a ha => ?_` and prove the remaining obligations.

Establish `ha0 : (a : ℂ) ≠ 0`. Establish `h1` using `(Finset.mem_Ioc.mp ha).1`. Conclude with `h1.ne'` after adjusting the coercions. Establish `hd0' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd0.ne'`. Clear the denominators using the available nonvanishing facts.
-/
theorem cF_eq (N : ℕ) :
    cF χ N = ∑ b ∈ Ioc 0 N, χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) := by
  have hcond : ∀ (n d : ℕ), n ∈ Finset.Ioc 0 N ∧ d ∈ n.divisors ↔
      n ∈ (Finset.Ioc 0 N).filter (d ∣ ·) ∧ d ∈ Finset.Ioc 0 N := by
    intro n d
    simp only [Finset.mem_Ioc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, hdn, -⟩
      have h1 := Nat.le_of_dvd hn0 hdn
      have h2 := Nat.pos_of_dvd_of_pos hdn hn0
      exact ⟨⟨⟨hn0, hnN⟩, hdn⟩, h2, by omega⟩
    · rintro ⟨⟨⟨hn0, hnN⟩, hdn⟩, -, -⟩
      exact ⟨⟨hn0, hnN⟩, hdn, by omega⟩
  unfold cF hH
  simp only [Finset.sum_div]
  rw [Finset.sum_comm' hcond]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
  have himg : (Finset.Ioc 0 N).filter (d ∣ ·) = (Finset.Ioc 0 (N / d)).image (fun a => d * a) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨a, rfl⟩⟩
      refine ⟨a, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos a with h | h
        · subst h
          simp at h1
        · exact h
      · exact (Nat.le_div_iff_mul_le hd0).mpr (by rw [mul_comm]; exact h2)
    · rintro ⟨a, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨Nat.mul_pos hd0 h1, ?_⟩, dvd_mul_right d a⟩
      have h3 := (Nat.le_div_iff_mul_le hd0).mp h2
      rw [mul_comm]
      exact h3
  rw [himg, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd0 h)]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha0 : (a : ℂ) ≠ 0 := by
    have h1 := (Finset.mem_Ioc.mp ha).1
    exact_mod_cast h1.ne'
  have hd0' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  field_simp

/- English proof (translation)
Rewrite using `[cF_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUN]`. Use `congr 1`. Establish `hcond : ∀ (b a : ℕ), b ∈ Finset.Ioc U N ∧ a ∈ Finset.Ioc 0 (N / b) ↔ b ∈ Finset.Ioc U (N / a) ∧ a ∈ Finset.Ioc 0 N`. Introduce `b a`. Simplify using `only [Finset.mem_Ioc]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hUb, hbN⟩, ha0, haN⟩`. Establish `hb0 : 0 < b` using `by omega`. Establish `h1 : a * b ≤ N` using `(Nat.le_div_iff_mul_le hb0).mp haN`. Use `⟨⟨hUb, (Nat.le_div_iff_mul_le ha0).mpr (by linarith)⟩, ha0, ?_⟩` and prove the remaining obligations.

Conclude with `le_trans (Nat.le_mul_of_pos_right a hb0) h1`. Introduce and unpack `⟨⟨hUb, hbNa⟩, ha0, haN⟩`. Establish `h1 : b * a ≤ N` using `(Nat.le_div_iff_mul_le ha0).mp hbNa`. Establish `hb0 : 0 < b` using `by omega`. Conclude with `⟨⟨hUb, le_trans (Nat.le_mul_of_pos_right b ha0) h1⟩, ha0, (Nat.le_div_iff_mul_le hb0).mpr (by linarith)⟩`.

Unfold `hH`. Use `push_cast`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm' hcond]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cF_split (N U : ℕ) (hUN : U ≤ N) :
    cF χ N = ∑ b ∈ Ioc 0 U, χ (b : ZMod q) / (b : ℂ) * (hH (N / b) : ℂ) +
      ∑ a ∈ Ioc 0 N, ((a : ℂ))⁻¹ * ∑ b ∈ Ioc U (N / a), χ (b : ZMod q) / (b : ℂ) := by
  rw [cF_eq, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le U) hUN]
  congr 1
  have hcond : ∀ (b a : ℕ), b ∈ Finset.Ioc U N ∧ a ∈ Finset.Ioc 0 (N / b) ↔
      b ∈ Finset.Ioc U (N / a) ∧ a ∈ Finset.Ioc 0 N := by
    intro b a
    simp only [Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hUb, hbN⟩, ha0, haN⟩
      have hb0 : 0 < b := by omega
      have h1 : a * b ≤ N := (Nat.le_div_iff_mul_le hb0).mp haN
      refine ⟨⟨hUb, (Nat.le_div_iff_mul_le ha0).mpr (by linarith)⟩, ha0, ?_⟩
      exact le_trans (Nat.le_mul_of_pos_right a hb0) h1
    · rintro ⟨⟨hUb, hbNa⟩, ha0, haN⟩
      have h1 : b * a ≤ N := (Nat.le_div_iff_mul_le ha0).mp hbNa
      have hb0 : 0 < b := by omega
      exact ⟨⟨hUb, le_trans (Nat.le_mul_of_pos_right b ha0) h1⟩, ha0,
        (Nat.le_div_iff_mul_le hb0).mpr (by linarith)⟩
  unfold hH
  push_cast
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm' hcond]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
