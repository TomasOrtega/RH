import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL
namespace GlobalTheory

/- English proof (translation)
Establish `hex : ∃ c, y c ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hy (by ext c; simpa using h c)`. Take `⟨c, hc, hmin⟩` from `(wellFounded_lt (α := Fin (n + 1))).has_min {c | y c ≠ 0} hex`.

Establish `hlt : ∀ d, d < c → y d = 0` using `fun d hd => by`. Assume the negation of the conclusion as `h`. Conclude with `hmin d h hd`. Unfold `IsHW at hw ⊢`. Take `⟨hd, hu⟩` from `hw`.

Establish `hc' : y c ≠ 0` using `hc`. Establish `hdiag : ∀ a, E a a (y c) = (θ a + if a = c then 1 else 0) • y c`. Introduce `a`. Establish `h` using `hEt a a y c`. Rewrite `h` using `[hd a, PiLp.smul_apply]`.

Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality. Simplify using `only [if_true] at h ⊢`. Rewrite using `[add_smul, one_smul, h, sub_add_cancel]`. Establish `hca : ¬ c = a` using `fun e => hac e.symm`.

Simplify using `only [hac, hca, if_false, sub_zero, add_zero] at h ⊢`. Conclude with `h.symm`. Use `⟨c, hc', ⟨hdiag, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Establish `h` using `hEt a b y c`.

Rewrite `h` using `[hu a b hab, PiLp.zero_apply]`. Distinguish the cases in `hcb : c = b`. Substitute `hcb` using the available equality. Simplify using `only [if_true, hlt a hab, sub_zero] at h`. Conclude with `h.symm`.

Simplify using `only [hcb, if_false, sub_zero] at h`. Conclude with `h.symm`. Establish `h` using `hOm y c`. Rewrite `h` using `[hl, PiLp.smul_apply]`. Establish `hterm : ∀ d, E c d (y d) = ((if d = c then θ c + 1 else 0) + (if c < d then (1 : ℂ) else 0)) • y c`.

Introduce `d`. Break down `lt_trichotomy d c with hdc | hdc | hdc` into its components or cases. Simplify using `[hlt d hdc, hdc.ne, hdc.not_gt]`. Substitute `hdc` using the available equality. Simplify using `[hdiag d]`.

Establish `h2` using `hEt c d y d`. Rewrite `h2` using `[hu c d hdc, PiLp.zero_apply]`. Simplify using `only [if_true] at h2`. Establish `h3` using `(sub_eq_zero.mp h2.symm)`. Simplify using `[h3, hdc, hdc.ne']`.

Rewrite `h` using `[hterm]`. Rewrite `h` using `[← Finset.sum_smul]`. Establish `h4` using `smul_left_injective ℂ hc' h`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_boole] at h4`. Establish `h5 : (Finset.univ.filter (fun d : Fin (n + 1) => c < d)).card = n - c`.

Establish `: Finset.univ.filter (fun d : Fin (n + 1) => c < d) = Finset.Ioi c`. Use extensionality with `d`. Simplify using the standard rewrite rules. Rewrite using `[this, Fin.card_Ioi]`. Use linear arithmetic over natural numbers and integers.

Rewrite `h4` using `[h5, Nat.cast_sub (Nat.lt_succ_iff.mp c.2)]`. Rewrite using `[h4]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hw_component_tensor_dual_standard (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (θ : Fin (n + 1) → ℂ) (lam : ℂ) (y : (PiLp 2 (fun _ : Fin (n + 1) => V))) (hEt : ∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) (hOm : ∀ y a, Om y a = ∑ c, E a c (y c)) (hy : y ≠ 0) (hw : IsHW Et θ y) (hl : Om y = lam • y) : ∃ c, y c ≠ 0 ∧ IsHW E (fun a => θ a + if a = c then 1 else 0) (y c) ∧ lam = θ c + 1 - ((c : ℕ) : ℂ) + (n : ℂ) := by
  classical
  have hex : ∃ c, y c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (by ext c; simpa using h c)
  obtain ⟨c, hc, hmin⟩ := (wellFounded_lt (α := Fin (n + 1))).has_min {c | y c ≠ 0} hex
  have hlt : ∀ d, d < c → y d = 0 := fun d hd => by
    by_contra h
    exact hmin d h hd
  unfold IsHW at hw ⊢
  obtain ⟨hd, hu⟩ := hw
  have hc' : y c ≠ 0 := hc
  have hdiag : ∀ a, E a a (y c) = (θ a + if a = c then 1 else 0) • y c := by
    intro a
    have h := hEt a a y c
    rw [hd a, PiLp.smul_apply] at h
    by_cases hac : a = c
    · subst hac
      simp only [if_true] at h ⊢
      rw [add_smul, one_smul, h, sub_add_cancel]
    · have hca : ¬ c = a := fun e => hac e.symm
      simp only [hac, hca, if_false, sub_zero, add_zero] at h ⊢
      exact h.symm
  refine ⟨c, hc', ⟨hdiag, ?_⟩, ?_⟩
  · intro a b hab
    have h := hEt a b y c
    rw [hu a b hab, PiLp.zero_apply] at h
    by_cases hcb : c = b
    · subst hcb
      simp only [if_true, hlt a hab, sub_zero] at h
      exact h.symm
    · simp only [hcb, if_false, sub_zero] at h
      exact h.symm
  · have h := hOm y c
    rw [hl, PiLp.smul_apply] at h
    have hterm : ∀ d, E c d (y d) =
        ((if d = c then θ c + 1 else 0) + (if c < d then (1 : ℂ) else 0)) • y c := by
      intro d
      rcases lt_trichotomy d c with hdc | hdc | hdc
      · simp [hlt d hdc, hdc.ne, hdc.not_gt]
      · subst hdc
        simp [hdiag d]
      · have h2 := hEt c d y d
        rw [hu c d hdc, PiLp.zero_apply] at h2
        simp only [if_true] at h2
        have h3 := (sub_eq_zero.mp h2.symm)
        simp [h3, hdc, hdc.ne']
    simp_rw [hterm] at h
    rw [← Finset.sum_smul] at h
    have h4 := smul_left_injective ℂ hc' h
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_boole] at h4
    have h5 : (Finset.univ.filter (fun d : Fin (n + 1) => c < d)).card = n - c := by
      have : Finset.univ.filter (fun d : Fin (n + 1) => c < d) = Finset.Ioi c := by
        ext d; simp
      rw [this, Fin.card_Ioi]; omega
    rw [h5, Nat.cast_sub (Nat.lt_succ_iff.mp c.2)] at h4
    rw [h4]; ring
end GlobalTheory
