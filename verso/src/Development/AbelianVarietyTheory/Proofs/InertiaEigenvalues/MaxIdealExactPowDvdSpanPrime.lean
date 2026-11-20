import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `L _ _ l e _ la hmax hin hout`. Establish `hex : ∃ k, ((l : ℕ) : 𝓞 L) ∉ la ^ (k + 1)` using `⟨e, hout⟩`. Establish `hspec : ((l : ℕ) : 𝓞 L) ∉ la ^ (Nat.find hex + 1)` using `Nat.find_spec hex`. Establish `hle : Nat.find hex ≤ e` using `Nat.find_min' hex hout`. Establish `hpos : 0 < Nat.find hex`.

Break down `Nat.eq_zero_or_pos (Nat.find hex) with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `hspec` using `[h, zero_add, pow_one]`. Conclude with `hspec hin`. Conclude with `h`.

Establish `hmem : ((l : ℕ) : 𝓞 L) ∈ la ^ Nat.find hex`. Establish `h1` using `Nat.find_min hex (Nat.sub_lt hpos one_pos)`. Rewrite `h1` using `[not_not]`. Establish `h4 : Nat.find hex - 1 + 1 = Nat.find hex` using `by omega`. Rewrite `h1` using `[h4]`. Then use the resulting hypothesis.

Establish `hdvd : la ^ Nat.find hex ∣ Ideal.span {((l : ℕ) : 𝓞 L)}`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hmem`. Take `⟨J, hJ⟩` from `hdvd`. Use `⟨Nat.find hex, J, hpos, hle, ?_, hJ⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Establish `hJle : J ≤ la`. Establish `h2` using `hmax.eq_of_le hne le_sup_left`. Combine the equalities or inequalities in the displayed calculation. Apply `hspec` to reduce the goal to its premises.

Establish `h3 : Ideal.span {((l : ℕ) : 𝓞 L)} ≤ la ^ (Nat.find hex + 1)`. Rewrite using `[hJ, pow_succ]`. Conclude with `Ideal.mul_mono_right hJle`. Conclude with `h3 (Ideal.subset_span (Set.mem_singleton _))`.
-/
theorem maxIdeal_exact_pow_dvd_span_prime : ∀ (L : Type) [Field L] [NumberField L] (l e : ℕ), l.Prime → ∀ (la : Ideal (𝓞 L)) [la.IsMaximal], ((l : ℕ) : 𝓞 L) ∈ la → ((l : ℕ) : 𝓞 L) ∉ la ^ (e + 1) → ∃ (e' : ℕ) (J : Ideal (𝓞 L)), 0 < e' ∧ e' ≤ e ∧ la ⊔ J = ⊤ ∧ Ideal.span {((l : ℕ) : 𝓞 L)} = la ^ e' * J := by
  intro L _ _ l e _ la hmax hin hout
  classical
  have hex : ∃ k, ((l : ℕ) : 𝓞 L) ∉ la ^ (k + 1) := ⟨e, hout⟩
  have hspec : ((l : ℕ) : 𝓞 L) ∉ la ^ (Nat.find hex + 1) := Nat.find_spec hex
  have hle : Nat.find hex ≤ e := Nat.find_min' hex hout
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso; rw [h, zero_add, pow_one] at hspec; exact hspec hin
    · exact h
  have hmem : ((l : ℕ) : 𝓞 L) ∈ la ^ Nat.find hex := by
    have h1 := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    rw [not_not] at h1
    have h4 : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rwa [h4] at h1
  have hdvd : la ^ Nat.find hex ∣ Ideal.span {((l : ℕ) : 𝓞 L)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hmem
  obtain ⟨J, hJ⟩ := hdvd
  refine ⟨Nat.find hex, J, hpos, hle, ?_, hJ⟩
  by_contra hne
  have hJle : J ≤ la := by
    have h2 := hmax.eq_of_le hne le_sup_left
    calc J ≤ la ⊔ J := le_sup_right
      _ = la := h2.symm
  apply hspec
  have h3 : Ideal.span {((l : ℕ) : 𝓞 L)} ≤ la ^ (Nat.find hex + 1) := by
    rw [hJ, pow_succ]; exact Ideal.mul_mono_right hJle
  exact h3 (Ideal.subset_span (Set.mem_singleton _))

end GlobalTheory
