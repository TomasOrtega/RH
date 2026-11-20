import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterInnerEqIntMulCard
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclicStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `G Γ _ _ _ _ φ s hp hs X hX Y hY z hz hnd hcos`. Use `haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩`. Use `haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm`. Establish `hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s`. Introduce `t`.

Rewrite using `[zpowers_eq_top_of_prime_card rfl hs]`. Discharge the goal by the elementary cases of `trivial`. Establish `hζ` using `Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero`. Take `⟨η, -, -, hfour⟩` from `GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic G Γ φ s hgen _ hζ`. Take `⟨h1, h2⟩` from `hfour X Y`.

Establish `hvirt : ∀ a : ℕ, (fun x => Y x * (η x : ℂ) ^ a) ∈ Virt ℂ ℂ (G ⋊[φ] Γ)`. Introduce `a`. Take `⟨hmul, -, -, -, hlin⟩` from `GlobalTheory.BI.virt_mul_comap_conj_ind_linear (G ⋊[φ] Γ)`. Use `hmul Y hY _ (hlin (η ^ a))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Establish `hm : ∀ a : ℕ, ∃ m : ℤ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = m * (Nat.card (G ⋊[φ] Γ) : ℂ)` using `fun a => GlobalTheory.BI.finsum_mul_star_virt_int _ X _ hX (hvirt a)`. Use `choose m hm using hm`. Establish `hN : Nat.card (G ⋊[φ] Γ) = Nat.card G * Nat.card Γ`.

Rewrite using `[Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]`. Establish `hG : (Nat.card G : ℂ) ≠ 0` using `by exact_mod_cast (Nat.card_pos (α := G)).ne'`. Establish `hl : (Nat.card Γ : ℂ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Simplify using `only [hm, hN, hcos, hz, mul_zero] at h1 h2`. Establish `hsum : ∑ i : Fin (Nat.card Γ), (m i.val : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ i.val = 0`.

Establish `h3 : ∑ a ∈ Finset.range (Nat.card Γ), (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a * (↑(m a) * ↑(Nat.card G * Nat.card Γ)) = (∑ a ∈ Finset.range (Nat.card Γ), (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a) * ((Nat.card G : ℂ) * Nat.card …`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h2` using `[h3]`. Rewrite using `[← Finset.sum_range (fun a => (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a)]`. Use `h2.symm` as an intermediate fact. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd h (mul_ne_zero hG hl)`. Establish `hall` using `(IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int hp hζ (fun i => m i.val)).1 hsum`. Establish `hconst : ∀ a ∈ Finset.range (Nat.card Γ), m a = m 0`. Introduce `a ha`. Conclude with `hall ⟨a, Finset.mem_range.1 ha⟩ ⟨0, hp.pos⟩`.

Rewrite `h1` using `[Finset.sum_congr rfl (fun a ha => by rw [hconst a ha])]`. Simplify using `only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1`. Establish `hz' : (z : ℂ) = (m 0 * Nat.card Γ : ℤ)`. Move the coercions through the operations in `at h1 ⊢`. Establish `h4 : (Nat.card Γ : ℂ) * (Nat.card G : ℂ) * ((z : ℂ) - m 0 * Nat.card Γ) = 0` using `by linear_combination h1`.

Break down `mul_eq_zero.1 h4 with h | h` into its components or cases. Conclude with `absurd h (mul_ne_zero hl hG)`. Conclude with `sub_eq_zero.1 h`. Conclude with `hnd ⟨m 0, by rw [mul_comm]; exact_mod_cast hz'⟩`.
-/
theorem finsum_coset_pair_ne_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ Y ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y (inl g)) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) ≠ 0 := by
  intro G Γ _ _ _ _ φ s hp hs X hX Y hY z hz hnd hcos
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  obtain ⟨η, -, -, hfour⟩ := GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic G Γ φ s hgen _ hζ
  obtain ⟨h1, h2⟩ := hfour X Y
  have hvirt : ∀ a : ℕ, (fun x => Y x * (η x : ℂ) ^ a) ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := by
    intro a
    obtain ⟨hmul, -, -, -, hlin⟩ := GlobalTheory.BI.virt_mul_comap_conj_ind_linear (G ⋊[φ] Γ)
    have := hmul Y hY _ (hlin (η ^ a))
    convert this using 1
    funext x; simp
  have hm : ∀ a : ℕ, ∃ m : ℤ, ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) = m * (Nat.card (G ⋊[φ] Γ) : ℂ) :=
    fun a => GlobalTheory.BI.finsum_mul_star_virt_int _ X _ hX (hvirt a)
  choose m hm using hm
  have hN : Nat.card (G ⋊[φ] Γ) = Nat.card G * Nat.card Γ := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hl : (Nat.card Γ : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  simp only [hm, hN, hcos, hz, mul_zero] at h1 h2
  have hsum : ∑ i : Fin (Nat.card Γ), (m i.val : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ i.val = 0 := by
    have h3 : ∑ a ∈ Finset.range (Nat.card Γ), (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a * (↑(m a) * ↑(Nat.card G * Nat.card Γ))
        = (∑ a ∈ Finset.range (Nat.card Γ), (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a) * ((Nat.card G : ℂ) * Nat.card Γ) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_; push_cast; ring
    rw [h3] at h2
    rw [← Finset.sum_range (fun a => (m a : ℂ) * (Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ))) ^ a)]
    have := h2.symm
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (mul_ne_zero hG hl)
  have hall := (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int hp hζ (fun i => m i.val)).1 hsum
  have hconst : ∀ a ∈ Finset.range (Nat.card Γ), m a = m 0 := by
    intro a ha
    exact hall ⟨a, Finset.mem_range.1 ha⟩ ⟨0, hp.pos⟩
  rw [Finset.sum_congr rfl (fun a ha => by rw [hconst a ha])] at h1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hz' : (z : ℂ) = (m 0 * Nat.card Γ : ℤ) := by
    push_cast at h1 ⊢
    have h4 : (Nat.card Γ : ℂ) * (Nat.card G : ℂ) * ((z : ℂ) - m 0 * Nat.card Γ) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h (mul_ne_zero hl hG)
    · exact sub_eq_zero.1 h
  exact hnd ⟨m 0, by rw [mul_comm]; exact_mod_cast hz'⟩

end GlobalTheory.Shin
