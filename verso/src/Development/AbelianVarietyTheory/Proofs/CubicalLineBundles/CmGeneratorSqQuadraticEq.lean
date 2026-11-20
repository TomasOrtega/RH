import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

open NumberField

namespace GlobalTheory.CMGeneratorSquare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hd : (H.d + 1) = 4 * ((H.d + 1) / 4)`. Use `H.d_mod` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h1 : (4 : 𝓞 E) * (H.w0 * H.w0) = 4 * (H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E))`. Establish `h2` using `H.two_weight_eq_one_add_root`.

Establish `h3` using `H.rt_sq`. Establish `h4 : ((H.d + 1 : ℕ) : 𝓞 E) = 4 * (((H.d + 1) / 4 : ℕ) : 𝓞 E)` using `by conv_lhs => rw [hd]`. Rewrite using `[Nat.cast_mul, Nat.cast_ofNat]`. Establish `h5 : (4 : 𝓞 E) * (H.w0 * H.w0) = (2 * H.w0) ^ 2` using `by ring`. Rewrite using `[h5, h2, mul_sub, ← h4]`.

Use `push_cast`. Take the linear combination `h3 - 2 * h2`. Establish `h4ne : (4 : 𝓞 E) ≠ 0` using `by exact_mod_cast (by norm_num : (4 : ℕ) ≠ 0)`. Conclude with `mul_left_cancel₀ h4ne h1`.
-/
theorem cm_generator_sq_quadratic_eq (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    H.w0 * H.w0 = H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
  have hd : (H.d + 1) = 4 * ((H.d + 1) / 4) := by
    have := H.d_mod; omega
  have h1 : (4 : 𝓞 E) * (H.w0 * H.w0) = 4 * (H.w0 - (((H.d + 1) / 4 : ℕ) : 𝓞 E)) := by
    have h2 := H.two_weight_eq_one_add_root
    have h3 := H.rt_sq
    have h4 : ((H.d + 1 : ℕ) : 𝓞 E) = 4 * (((H.d + 1) / 4 : ℕ) : 𝓞 E) := by
      conv_lhs => rw [hd]
      rw [Nat.cast_mul, Nat.cast_ofNat]
    have h5 : (4 : 𝓞 E) * (H.w0 * H.w0) = (2 * H.w0) ^ 2 := by ring
    rw [h5, h2, mul_sub, ← h4]
    push_cast
    linear_combination h3 - 2 * h2
  have h4ne : (4 : 𝓞 E) ≠ 0 := by exact_mod_cast (by norm_num : (4 : ℕ) ≠ 0)
  exact mul_left_cancel₀ h4ne h1

/- English proof (translation)
Introduce `E _ _ _ H a ha`. Use `set k : ℤ := (((H.d + 1) / 4 : ℕ) : ℤ) with hk`. Establish `hsq : H.w0 * H.w0 = H.w0 - (k : 𝓞 E)` using `by rw [cm_generator_sq_quadratic_eq H, hk, Int.cast_natCast]`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Rewrite `hx` using `[Set.mem_singleton_iff]`. Conclude with `⟨0, 1, by rw [hx]; push_cast; ring⟩`. Consider the case `algebraMap r => exact ⟨r, 0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨u, v, rfl⟩` from `hx`.

Take `⟨u', v', rfl⟩` from `hy`. Conclude with `⟨u + u', v + v', by push_cast; ring⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨u, v, rfl⟩` from `hx`. Take `⟨u', v', rfl⟩` from `hy`.

Use `⟨u * u' - v * v' * k, u * v' + v * u' + v * v', ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `(v * v' : 𝓞 E) * hsq`.
-/
theorem main : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {a : NumberField.RingOfIntegers E}, a ∈ GlobalTheory.CM.OK H →
    ∃ (u : ℤ) (v : ℤ), a = (↑u : NumberField.RingOfIntegers E) + (↑v : NumberField.RingOfIntegers E) *
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.w0 H := by
  intro E _ _ _ H a ha
  set k : ℤ := (((H.d + 1) / 4 : ℕ) : ℤ) with hk
  have hsq : H.w0 * H.w0 = H.w0 - (k : 𝓞 E) := by rw [cm_generator_sq_quadratic_eq H, hk, Int.cast_natCast]
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by rw [hx]; push_cast; ring⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    refine ⟨u * u' - v * v' * k, u * v' + v * u' + v * v', ?_⟩
    push_cast
    linear_combination (v * v' : 𝓞 E) * hsq

end GlobalTheory.CMGeneratorSquare
