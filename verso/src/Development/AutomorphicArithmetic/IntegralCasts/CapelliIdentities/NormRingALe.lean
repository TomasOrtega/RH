import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qi27.muPrime :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Set ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ {ζ : ℂ_[l] | ∃ (n : ℕ), (0 : ℕ) < n ∧ ¬l ∣ n ∧ ζ ^ n = (1 : ℂ_[l])}

noncomputable def UpperTheory.Reformulated.B.Qi27.ringA :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Subring ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ Subring.closure (UpperTheory.Reformulated.B.Qi27.muPrime l)

/- English proof (translation)
Introduce `l hl x hx`. Unfold `UpperTheory.Reformulated.B.Qi27.ringA at hx`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem y hy`. Take `⟨n, hn, -, h⟩` from `hy`.

Establish `h1 : ‖y‖ ^ n = 1` using `by rw [← norm_pow, h, norm_one]`. Conclude with `((pow_eq_one_iff_of_nonneg (norm_nonneg y) hn.ne').1 h1).le`. Consider the case `zero => simp`. Consider the case `one => simp`. Consider the case `add a b _ _ ha hb => exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)`.

Consider the case `neg a _ ha => simpa using ha`. Consider the case `mul a b _ _ ha hb`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ ha (norm_nonneg b) hb`.
-/
theorem UpperTheory.Reformulated.B.Qi27.norm_ringA_le :
    ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {x : ℂ_[l]}, x ∈ UpperTheory.Reformulated.B.Qi27.ringA l → ‖x‖ ≤ (1 : ℝ) := by
  intro l hl x hx
  unfold UpperTheory.Reformulated.B.Qi27.ringA at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨n, hn, -, h⟩ := hy
    have h1 : ‖y‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg y) hn.ne').1 h1).le
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  | neg a _ ha => simpa using ha
  | mul a b _ _ ha hb =>
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg b) hb
