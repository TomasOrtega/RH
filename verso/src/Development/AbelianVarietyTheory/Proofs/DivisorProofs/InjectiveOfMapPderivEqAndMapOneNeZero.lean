import Mathlib

namespace GlobalTheory.FockAlg

open MvPolynomial in

/- English proof (translation)
Establish `hC : ∀ p : MvPolynomial ι ℂ, Φ₀ p = 0 → (∀ m ∈ p.support, m = 0) → p = 0`. Introduce `p hp hs`. Establish `e : p = (coeff 0 p) • (1 : MvPolynomial ι ℂ)`. Use extensionality with `m`. Distinguish the cases in `hm : m = 0`.

Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Establish `: coeff m p = 0`. Assume the negation of the conclusion as `h`. Conclude with `hm (hs m (mem_support_iff.2 h))`.

Rewrite using `[this, coeff_smul, coeff_one, if_neg (Ne.symm hm), smul_zero]`. Rewrite `hp` using `[e, map_smul, smul_eq_zero]`. Break down `hp with hp | hp` into its components or cases. Rewrite using `[e, hp, zero_smul]`. Conclude with `absurd hp h1`.

Establish `key : ∀ n : ℕ, ∀ p : MvPolynomial ι ℂ, (∀ m ∈ p.support, m.degree ≤ n) → Φ₀ p = 0 → p = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p hs hp`.

Conclude with `hC p hp (fun m hm => (Finsupp.degree_eq_zero_iff m).1 (Nat.le_zero.1 (hs m hm)))`. Consider the case `succ n ih`. Introduce `p hs hp`. Establish `hz : ∀ i, pderiv i p = 0`. Introduce `i`.

Apply `ih` to reduce the goal to its premises. Introduce `m hm`. Rewrite `hm` using `[mem_support_iff, coeff_pderiv]`. Establish `h2` using `hs _ (mem_support_iff.2 (left_ne_zero_of_mul hm))`. Rewrite `h2` using `[map_add, Finsupp.degree_single]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hd, hp, map_zero]`. Apply `hC p hp` to reduce the goal to its premises. Introduce `m hm`. Assume the negation of the conclusion as `hm0`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, m i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hm0 (Finsupp.ext h)`. Establish `hle : Finsupp.single i 1 ≤ m`.

Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers. Establish `hc` using `congrArg (coeff (m - Finsupp.single i 1)) (hz i)`. Rewrite `hc` using `[coeff_pderiv, tsub_add_cancel_of_le hle, coeff_zero, mul_eq_zero]`. Break down `hc with hc | hc` into its components or cases.

Conclude with `(mem_support_iff.1 hm) hc`. Conclude with `(Nat.cast_add_one_ne_zero _) hc`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `p hp`. Conclude with `key (p.support.sup fun m => m.degree) p (fun m hm => Finset.le_sup (f := fun m : ι →₀ ℕ => m.degree) hm) hp`.
-/
theorem injective_of_pderiv {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type}
    (Φ₀ : MvPolynomial ι ℂ →ₗ[ℂ] V) (d : ι → Module.End ℂ V)
    (hd : ∀ (i : ι) (p : MvPolynomial ι ℂ), Φ₀ (MvPolynomial.pderiv i p) = d i (Φ₀ p))
    (h1 : Φ₀ 1 ≠ 0) : Function.Injective Φ₀ := by
  classical
  have hC : ∀ p : MvPolynomial ι ℂ, Φ₀ p = 0 → (∀ m ∈ p.support, m = 0) → p = 0 := by
    intro p hp hs
    have e : p = (coeff 0 p) • (1 : MvPolynomial ι ℂ) := by
      ext m
      by_cases hm : m = 0
      · subst hm; simp
      · have : coeff m p = 0 := by
          by_contra h
          exact hm (hs m (mem_support_iff.2 h))
        rw [this, coeff_smul, coeff_one, if_neg (Ne.symm hm), smul_zero]
    rw [e, map_smul, smul_eq_zero] at hp
    rcases hp with hp | hp
    · rw [e, hp, zero_smul]
    · exact absurd hp h1
  have key : ∀ n : ℕ, ∀ p : MvPolynomial ι ℂ, (∀ m ∈ p.support, m.degree ≤ n) →
      Φ₀ p = 0 → p = 0 := by
    intro n
    induction n with
    | zero =>
      intro p hs hp
      exact hC p hp (fun m hm => (Finsupp.degree_eq_zero_iff m).1 (Nat.le_zero.1 (hs m hm)))
    | succ n ih =>
      intro p hs hp
      have hz : ∀ i, pderiv i p = 0 := by
        intro i
        apply ih
        · intro m hm
          rw [mem_support_iff, coeff_pderiv] at hm
          have h2 := hs _ (mem_support_iff.2 (left_ne_zero_of_mul hm))
          rw [map_add, Finsupp.degree_single] at h2
          omega
        · rw [hd, hp, map_zero]
      apply hC p hp
      intro m hm
      by_contra hm0
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra h
        push Not at h
        exact hm0 (Finsupp.ext h)
      have hle : Finsupp.single i 1 ≤ m := by
        rw [Finsupp.single_le_iff]; omega
      have hc := congrArg (coeff (m - Finsupp.single i 1)) (hz i)
      rw [coeff_pderiv, tsub_add_cancel_of_le hle, coeff_zero, mul_eq_zero] at hc
      rcases hc with hc | hc
      · exact (mem_support_iff.1 hm) hc
      · exact (Nat.cast_add_one_ne_zero _) hc
  rw [injective_iff_map_eq_zero]
  intro p hp
  exact key (p.support.sup fun m => m.degree) p
    (fun m hm => Finset.le_sup (f := fun m : ι →₀ ℕ => m.degree) hm) hp

end GlobalTheory.FockAlg
