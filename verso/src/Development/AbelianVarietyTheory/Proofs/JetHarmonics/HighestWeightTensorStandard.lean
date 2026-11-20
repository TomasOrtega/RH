import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _ n E Et Om θ lam y hEt hOm hy hw hlam`. Take `⟨h1, h2⟩` from `hw`. Establish `hne : (Finset.univ.filter (fun c => y c ≠ 0)).Nonempty`. Assume the negation of the conclusion as `h`. Apply `hy` to reduce the goal to its premises.

Use extensionality with `c`. Assume the negation of the conclusion as `hc`. Conclude with `h ⟨c, by simpa using hc⟩`. Take `⟨c, hc, hmax⟩` from `Finset.exists_max_image _ id hne`. Establish `hc0 : y c ≠ 0` using `by simpa using hc`.

Establish `hz : ∀ d, c < d → y d = 0`. Introduce `d hd`. Assume the negation of the conclusion as `h`. Conclude with `absurd (hmax d (by simpa using h)) (not_le.mpr hd)`. Establish `hup : ∀ a b, a < b → ∀ e, E a b (y e) = - if e = a then y b else 0`.

Introduce `a b hab e`. Establish `h` using `hEt a b y e`. Establish `h0 : Et a b y = 0` using `h2 a b hab`. Rewrite `h` using `[h0]`. Conclude with `eq_neg_of_add_eq_zero_left h.symm`.

Establish `hdiag : ∀ a, E a a (y c) = (θ a - if a = c then 1 else 0) • y c`. Introduce `a`. Establish `h` using `hEt a a y c`. Establish `h0 : Et a a y = θ a • y` using `h1 a`. Rewrite `h` using `[h0]`.

Establish `h' : E a a (y c) = θ a • y c - if c = a then y a else 0`. Rewrite using `[eq_sub_iff_add_eq, ← h]`. Both sides reduce to the same expression. Rewrite using `[h']`. Distinguish the cases in `hca : c = a`.

Substitute `hca` using the available equality. Simplify using `[sub_smul]`. Simplify using `[hca, Ne.symm hca]`. Establish `hraise : ∀ a b, a < b → E a b (y c) = 0`. Introduce `a b hab`.

Rewrite using `[hup a b hab c]`. Distinguish the cases in `hca : c = a`. Substitute `hca` using the available equality. Simplify using `[hz b hab]`. Simplify using `[hca]`.

Use `⟨c, hc0, ⟨hdiag, hraise⟩, ?_⟩` and prove the remaining obligations. Establish `hterm : ∀ d, E d c (y d) = ((if d = c then θ c - 1 else 0) - if d < c then 1 else 0 : ℂ) • y c`. Introduce `d`. Break down `lt_trichotomy d c with h | h | h` into its components or cases. Rewrite using `[hup d c h d]`.

Simplify using `[h, h.ne]`. Substitute `h` using the available equality. Rewrite using `[hdiag]`. Simplify using the standard rewrite rules. Simplify using `[hz d h, h.ne', not_lt.mpr h.le]`.

Establish `hsum : lam • y c = (θ c - 1 - ((c : ℕ) : ℂ)) • y c`. Establish `h` using `hOm y c`. Rewrite `h` using `[hlam]`. Establish `h' : lam • y c = ∑ d, E d c (y d)` using `h`. Rewrite using `[h', Finset.sum_congr rfl (fun d _ => hterm d), ← Finset.sum_smul, Finset.sum_sub_distrib]`.

Use `congr 2`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_boole]`. Establish `: Finset.univ.filter (fun d => d < c) = Finset.Iio c` using `by ext d; simp`. Rewrite using `[this, Fin.card_Iio]`.

Conclude with `smul_left_injective ℂ hc0 hsum`.
-/
theorem highestWeight_tensor_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (θ : Fin (n + 1) → ℂ) (lam : ℂ) (y : (PiLp 2 (fun _ : Fin (n + 1) => V))), (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → y ≠ 0 → IsHW Et θ y → Om y = lam • y → ∃ c, y c ≠ 0 ∧ IsHW E (fun a => θ a - if a = c then 1 else 0) (y c) ∧ lam = θ c - 1 - ((c : ℕ) : ℂ) := by
  classical
  intro V _ _ _ n E Et Om θ lam y hEt hOm hy hw hlam
  obtain ⟨h1, h2⟩ := hw
  have hne : (Finset.univ.filter (fun c => y c ≠ 0)).Nonempty := by
    by_contra h
    apply hy
    ext c
    by_contra hc
    exact h ⟨c, by simpa using hc⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image _ id hne
  have hc0 : y c ≠ 0 := by simpa using hc
  have hz : ∀ d, c < d → y d = 0 := by
    intro d hd
    by_contra h
    exact absurd (hmax d (by simpa using h)) (not_le.mpr hd)
  have hup : ∀ a b, a < b → ∀ e, E a b (y e) = - if e = a then y b else 0 := by
    intro a b hab e
    have h := hEt a b y e
    have h0 : Et a b y = 0 := h2 a b hab
    rw [h0] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hdiag : ∀ a, E a a (y c) = (θ a - if a = c then 1 else 0) • y c := by
    intro a
    have h := hEt a a y c
    have h0 : Et a a y = θ a • y := h1 a
    rw [h0] at h
    have h' : E a a (y c) = θ a • y c - if c = a then y a else 0 := by
      rw [eq_sub_iff_add_eq, ← h]; rfl
    rw [h']
    by_cases hca : c = a
    · subst hca; simp [sub_smul]
    · simp [hca, Ne.symm hca]
  have hraise : ∀ a b, a < b → E a b (y c) = 0 := by
    intro a b hab
    rw [hup a b hab c]
    by_cases hca : c = a
    · subst hca; simp [hz b hab]
    · simp [hca]
  refine ⟨c, hc0, ⟨hdiag, hraise⟩, ?_⟩
  have hterm : ∀ d, E d c (y d) =
      ((if d = c then θ c - 1 else 0) - if d < c then 1 else 0 : ℂ) • y c := by
    intro d
    rcases lt_trichotomy d c with h | h | h
    · rw [hup d c h d]; simp [h, h.ne]
    · subst h; rw [hdiag]; simp
    · simp [hz d h, h.ne', not_lt.mpr h.le]
  have hsum : lam • y c = (θ c - 1 - ((c : ℕ) : ℂ)) • y c := by
    have h := hOm y c
    rw [hlam] at h
    have h' : lam • y c = ∑ d, E d c (y d) := h
    rw [h', Finset.sum_congr rfl (fun d _ => hterm d), ← Finset.sum_smul,
      Finset.sum_sub_distrib]
    congr 2
    · simp
    · rw [Finset.sum_boole]
      have : Finset.univ.filter (fun d => d < c) = Finset.Iio c := by ext d; simp
      rw [this, Fin.card_Iio]
  exact smul_left_injective ℂ hc0 hsum

end GlobalTheory
