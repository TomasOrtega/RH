import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
open Formalism.L2.Theta

namespace GlobalTheory.SignedHC.GridData

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Break down `eq_or_lt_of_le hk with h | h` into its components or cases. Rewrite using `[h]`. Conclude with `le_of_lt (G.v_anti i G.k h2 h le_rfl)`. Break down `eq_or_lt_of_le h2 with h | h` into its components or cases.

Rewrite using `[← h]`. Conclude with `le_of_lt (G.v_anti 2 i le_rfl h hk)`.
-/
theorem v_bounds_of_mem (G : GridData) {i : ℕ} (h2 : 2 ≤ i) (hk : i ≤ G.k) : G.v G.k ≤ G.v i ∧ G.v i ≤ G.v 2 := by
  constructor
  · rcases eq_or_lt_of_le hk with h | h
    · rw [h]
    · exact le_of_lt (G.v_anti i G.k h2 h le_rfl)
  · rcases eq_or_lt_of_le h2 with h | h
    · rw [← h]
    · exact le_of_lt (G.v_anti 2 i le_rfl h hk)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Break down `eq_or_lt_of_le h1 with h | h` into its components or cases. Rewrite using `[← h]`. Conclude with `le_of_lt (G.b_mono 1 l le_rfl h hm)`. Break down `eq_or_lt_of_le hm with h | h` into its components or cases.

Rewrite using `[h]`. Conclude with `le_of_lt (G.b_mono l G.m h1 h le_rfl)`.
-/
theorem b_bounds_of_mem (G : GridData) {l : ℕ} (h1 : 1 ≤ l) (hm : l ≤ G.m) : G.b 1 ≤ G.b l ∧ G.b l ≤ G.b G.m := by
  constructor
  · rcases eq_or_lt_of_le h1 with h | h
    · rw [← h]
    · exact le_of_lt (G.b_mono 1 l le_rfl h hm)
  · rcases eq_or_lt_of_le hm with h | h
    · rw [h]
    · exact le_of_lt (G.b_mono l G.m h1 h le_rfl)

/- English proof (translation)
The claim follows from `|x.1| ≤ G.a 0 := by have hv2 : (0 : ℚ) ≤ G.v 2 := by have := (G.v_bounds_of_mem le_rfl G.two_le_k).1 exact_mod_cast hv.trans this have hga : (0 : ℚ) ≤ G.ga := by positivity rcases G.mem_lam.1 hx with ⟨l, hl, rfl⟩ | ⟨hc, -⟩ · have e := G.a_sub_a 0 l simp only [Nat.cast_zero, sub_z …`.
-/
theorem abs_le_a_zero_of_mem_lam (G : GridData) (hv : 0 ≤ G.v G.k) {x : ℚ × Bool} (hx : x ∈ G.lam) :
    |x.1| ≤ G.a 0 := by
  have hv2 : (0 : ℚ) ≤ G.v 2 := by
    have := (G.v_bounds_of_mem le_rfl G.two_le_k).1
    exact_mod_cast hv.trans this
  have hga : (0 : ℚ) ≤ G.ga := by positivity
  rcases G.mem_lam.1 hx with ⟨l, hl, rfl⟩ | ⟨hc, -⟩
  · have e := G.a_sub_a 0 l
    simp only [Nat.cast_zero, sub_zero] at e
    have hm := G.a_m
    have e2 := G.a_sub_a l G.m
    have hl' : (l : ℚ) ≤ G.m := by exact_mod_cast hl
    have hl0 : (0 : ℚ) ≤ l := by positivity
    have h1 : (0 : ℚ) ≤ (l : ℚ) * G.ga := mul_nonneg hl0 hga
    have h2 : (0 : ℚ) ≤ ((G.m : ℚ) - l) * G.ga := mul_nonneg (by linarith) hga
    simp only
    rw [abs_le]; constructor <;> linarith
  · obtain ⟨i, h2, hk, e⟩ := G.mem_cloudHalf.1 hc
    obtain ⟨hlo, hhi⟩ := G.v_bounds_of_mem h2 hk
    have hlo' : (0 : ℚ) ≤ G.v i := by exact_mod_cast hv.trans hlo
    have hhi' : (G.v i : ℚ) ≤ G.v 2 := by exact_mod_cast hhi
    have ha0 : G.a 0 = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1) * G.ga := by simp [a]
    have h3 : (0 : ℚ) ≤ ((G.m : ℚ) + 1) * G.ga := by positivity
    rw [e, vHalf, abs_le]; constructor <;> linarith

/- English proof (translation)
The claim follows from `|x.1| ≤ G.a 0 ∨ |x.1| ≤ G.b G.m := by rcases G.mem_discrete_parameter_iff.1 hx with ⟨hc, -⟩ | ⟨l, h1, hm, rfl⟩ · left obtain ⟨i, h2, hk, e⟩ := G.mem_cloud.1 hc obtain ⟨hlo, hhi⟩ := G.v_bounds_of_mem h2 hk have hlo' : (0 : ℚ) ≤ G.v i := by exact_mod_cast hv.trans hlo have hhi' : ( …`.
-/
theorem abs_le_of_mem_D0 (G : GridData) (hv : 0 ≤ G.v G.k) (hb : 0 < G.b 1) {x : ℚ × Bool} (hx : x ∈ G.parD0) :
    |x.1| ≤ G.a 0 ∨ |x.1| ≤ G.b G.m := by
  rcases G.mem_discrete_parameter_iff.1 hx with ⟨hc, -⟩ | ⟨l, h1, hm, rfl⟩
  · left
    obtain ⟨i, h2, hk, e⟩ := G.mem_cloud.1 hc
    obtain ⟨hlo, hhi⟩ := G.v_bounds_of_mem h2 hk
    have hlo' : (0 : ℚ) ≤ G.v i := by exact_mod_cast hv.trans hlo
    have hhi' : (G.v i : ℚ) ≤ G.v 2 := by exact_mod_cast hhi
    have ha0 : G.a 0 = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1) * G.ga := by simp [a]
    have h3 : (0 : ℚ) ≤ ((G.m : ℚ) + 1) * G.ga := by positivity
    rw [e, abs_le]; constructor <;> linarith
  · right
    obtain ⟨hlo, hhi⟩ := G.b_bounds_of_mem h1 hm
    have hlo' : (0 : ℚ) < G.b l := by exact_mod_cast hb.trans_le hlo
    have hhi' : (G.b l : ℚ) ≤ G.b G.m := by exact_mod_cast hhi
    simp only
    rw [abs_le]; constructor <;> linarith

end GlobalTheory.SignedHC.GridData

namespace GlobalTheory.Twist

open GlobalTheory.SignedHC

/- English proof (translation)
Introduce `G n lam ε mu ε' B hv hb hA hBm hP hD`. Take `⟨-, q, hq, hS⟩` from `hP`. Take `⟨-, q', hq', hS'⟩` from `hD`. Prove the components needed by the constructor for the conclusion. Introduce `a`.

Establish `hmem : (q a, ε a) ∈ G.lam`. Rewrite using `[← G.parPi_zero, hS]`. Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ a)`. Establish `h` using `G.abs_le_a_zero_of_mem_lam hv hmem`. Rewrite using `[hq a]`.

Establish `h' : |((q a : ℚ) : ℝ)| ≤ ((G.a 0 : ℚ) : ℝ)` using `by rw [← Rat.cast_abs]; exact_mod_cast h`. Conclude with `h'.trans hA`. Introduce `i`. Establish `hmem : (q' i, ε' i) ∈ G.parD0`. Rewrite using `[hS']`.

Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ i)`. Rewrite using `[hq' i]`. Break down `G.abs_le_of_mem_D0 hv hb hmem with h | h` into its components or cases. Establish `h' : |((q' i : ℚ) : ℝ)| ≤ ((G.a 0 : ℚ) : ℝ)` using `by rw [← Rat.cast_abs]; exact_mod_cast h`. Conclude with `h'.trans hA`.

Establish `h' : |((q' i : ℚ) : ℝ)| ≤ ((G.b G.m : ℤ) : ℝ)`. Rewrite using `[← Rat.cast_abs]`. Establish `: ((G.b G.m : ℤ) : ℝ) = (((G.b G.m : ℤ) : ℚ) : ℝ)` using `by push_cast; rfl`. Rewrite using `[this]`. Conclude with `h` after adjusting the coercions.

Conclude with `h'.trans hBm`.
-/
theorem parPi_parD0_entries_bounded : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ}
    {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {B : ℝ}, 0 ≤ G.v G.k → 0 < G.b 1 →
    ((G.a 0 : ℚ) : ℝ) ≤ B → (G.b G.m : ℝ) ≤ B → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' →
    (∀ a, |lam a| ≤ B) ∧ ∀ i, |mu i| ≤ B := by
  intro G n lam ε mu ε' B hv hb hA hBm hP hD
  obtain ⟨-, q, hq, hS⟩ := hP
  obtain ⟨-, q', hq', hS'⟩ := hD
  constructor
  · intro a
    have hmem : (q a, ε a) ∈ G.lam := by
      rw [← G.parPi_zero, hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    have h := G.abs_le_a_zero_of_mem_lam hv hmem
    rw [hq a]
    have h' : |((q a : ℚ) : ℝ)| ≤ ((G.a 0 : ℚ) : ℝ) := by rw [← Rat.cast_abs]; exact_mod_cast h
    exact h'.trans hA
  · intro i
    have hmem : (q' i, ε' i) ∈ G.parD0 := by
      rw [hS']; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rw [hq' i]
    rcases G.abs_le_of_mem_D0 hv hb hmem with h | h
    · have h' : |((q' i : ℚ) : ℝ)| ≤ ((G.a 0 : ℚ) : ℝ) := by rw [← Rat.cast_abs]; exact_mod_cast h
      exact h'.trans hA
    · have h' : |((q' i : ℚ) : ℝ)| ≤ ((G.b G.m : ℤ) : ℝ) := by
        rw [← Rat.cast_abs]
        have : ((G.b G.m : ℤ) : ℝ) = (((G.b G.m : ℤ) : ℚ) : ℝ) := by push_cast; rfl
        rw [this]; exact_mod_cast h
      exact h'.trans hBm

end GlobalTheory.Twist
