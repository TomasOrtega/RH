import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ σ _ A _ _ φ hφ a ha`. Use `haveI := Fintype.ofFinite σ`. Establish `hc : ∀ α : σ →₀ ℕ, ∃ o : Option σ, (α = 0 ∧ o = none) ∨ ∃ i, o = some i ∧ α i ≠ 0`. Introduce `α`. Distinguish the cases in `h : α = 0`.

Conclude with `⟨none, Or.inl ⟨h, rfl⟩⟩`. Take `⟨i, hi⟩` from `Finsupp.ne_iff.1 h`. Conclude with `⟨some i, Or.inr ⟨i, rfl, by simpa using hi⟩⟩`. Use `choose c hc using hc`. Set `g : σ → MvPowerSeries σ k` to `fun i α => if c α = some i then coeff α a else 0`.

Establish `hg : ∀ i α, coeff α (g i) = if c α = some i then coeff α a else 0` using `fun _ _ => rfl`. Establish `hsum : a = ∑ i, g i`. Use extensionality with `α`. Rewrite using `[map_sum]`. Simplify using `only [hg]`.

Break down `hc α with ⟨h0, h1⟩ | ⟨i, h1, -⟩` into its components or cases. Rewrite using `[h1, h0]`. Simplify using `using ha`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.

Rewrite using `[hsum, map_sum]`. Use `isNilpotent_sum fun i _ => ?_` and prove the remaining obligations. Establish `hd : (X i : MvPowerSeries σ k) ∣ g i`. Rewrite using `[X_dvd_iff]`. Introduce `m hm`.

Rewrite using `[hg, if_neg]`. Introduce `h`. Break down `hc m with ⟨-, h1⟩ | ⟨j, h1, h2⟩` into its components or cases. Rewrite `h` using `[h1]`. Consider the cases of `h`.

Rewrite `h` using `[h1]`. Consider the cases of `h`. Conclude with `h2 hm`. Take `⟨b, hb⟩` from `hd`. Rewrite using `[hb, map_mul]`.

Conclude with `(Commute.all _ _).isNilpotent_mul_right (hφ i)`.
-/
theorem mvPowerSeries_algHom_isNilpotent_of_constantCoeff_zero :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        ∀ a : MvPowerSeries σ k, constantCoeff a = 0 → IsNilpotent (φ a) := by
  intro k _ σ _ A _ _ φ hφ a ha
  classical
  haveI := Fintype.ofFinite σ
  have hc : ∀ α : σ →₀ ℕ, ∃ o : Option σ, (α = 0 ∧ o = none) ∨ ∃ i, o = some i ∧ α i ≠ 0 := by
    intro α
    by_cases h : α = 0
    · exact ⟨none, Or.inl ⟨h, rfl⟩⟩
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 h
      exact ⟨some i, Or.inr ⟨i, rfl, by simpa using hi⟩⟩
  choose c hc using hc
  let g : σ → MvPowerSeries σ k := fun i α => if c α = some i then coeff α a else 0
  have hg : ∀ i α, coeff α (g i) = if c α = some i then coeff α a else 0 := fun _ _ => rfl
  have hsum : a = ∑ i, g i := by
    ext α
    rw [map_sum]
    simp only [hg]
    rcases hc α with ⟨h0, h1⟩ | ⟨i, h1, -⟩
    · rw [h1, h0]
      simpa using ha
    · rw [h1]
      simp
  rw [hsum, map_sum]
  refine isNilpotent_sum fun i _ => ?_
  have hd : (X i : MvPowerSeries σ k) ∣ g i := by
    rw [X_dvd_iff]
    intro m hm
    rw [hg, if_neg]
    intro h
    rcases hc m with ⟨-, h1⟩ | ⟨j, h1, h2⟩
    · rw [h1] at h; cases h
    · rw [h1] at h
      cases h
      exact h2 hm
  obtain ⟨b, hb⟩ := hd
  rw [hb, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right (hφ i)

end GlobalTheory
