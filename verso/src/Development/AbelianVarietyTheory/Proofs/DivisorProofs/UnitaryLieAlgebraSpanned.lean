import Mathlib
open Matrix

namespace GlobalTheory.TracelessSkewSpan

variable {r : ℕ}

noncomputable def skewSub (A : Matrix (Fin r) (Fin r) ℂ) :
    Submodule ℝ (Matrix (Fin r) (Fin r) ℂ) where
  carrier := {Y | Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    have h : (X + Y).map (starRingEnd ℂ) = X.map (starRingEnd ℂ) + Y.map (starRingEnd ℂ) := by
      ext i j; simp
    rw [transpose_add, h, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᵀ * A + A * X.map (starRingEnd ℂ)) + (Yᵀ * A + A * Y.map (starRingEnd ℂ)) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c Y hY
    simp only [Set.mem_setOf_eq] at *
    have h1 : (c • Y).map (starRingEnd ℂ) = c • Y.map (starRingEnd ℂ) := by
      ext i j; simp [Complex.real_smul]
    rw [transpose_smul, h1, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY, smul_zero]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
lemma mem_skewSub {A Y : Matrix (Fin r) (Fin r) ℂ} :
    Y ∈ skewSub A ↔ Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0 := Iff.rfl

/- English proof (translation)
Rewrite `h1`, `h2` using `[mem_skewSub]`. Establish `hc : (Complex.I • Y).map (starRingEnd ℂ) = (-Complex.I) • Y.map (starRingEnd ℂ)`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite `h2` using `[transpose_smul, hc, Matrix.smul_mul, Matrix.mul_smul]`.

Establish `h3 : Yᵀ * A - A * Y.map (starRingEnd ℂ) = 0`. Establish `: Complex.I • (Yᵀ * A - A * Y.map (starRingEnd ℂ)) = 0`. Rewrite using `[smul_sub, ← h2, neg_smul]`. Normalize the expressions using the abelian group laws. Break down `smul_eq_zero.mp this with h | h` into its components or cases.

Conclude with `absurd h Complex.I_ne_zero`. Conclude with `h`. Establish `h4 : Yᵀ * A = 0`. Establish `: (2 : ℂ) • (Yᵀ * A) = 0`. Rewrite using `[two_smul]`.

Combine the equalities or inequalities in the displayed calculation. Break down `smul_eq_zero.mp this with h | h` into its components or cases. Evaluate the numerical expressions using `at h`. Conclude with `h`. Establish `hu : IsUnit A.det` using `isUnit_iff_ne_zero.mpr hA`.

Establish `h5 : Yᵀ = 0`. Combine the equalities or inequalities in the displayed calculation. Simplify using `using congrArg Matrix.transpose h5`.
-/
lemma eq_zero_of_mem_of_I_smul_mem {A Y : Matrix (Fin r) (Fin r) ℂ} (hA : A.det ≠ 0)
    (h1 : Y ∈ skewSub A) (h2 : Complex.I • Y ∈ skewSub A) : Y = 0 := by
  rw [mem_skewSub] at h1 h2
  have hc : (Complex.I • Y).map (starRingEnd ℂ) = (-Complex.I) • Y.map (starRingEnd ℂ) := by
    ext i j; simp
  rw [transpose_smul, hc, Matrix.smul_mul, Matrix.mul_smul] at h2
  have h3 : Yᵀ * A - A * Y.map (starRingEnd ℂ) = 0 := by
    have : Complex.I • (Yᵀ * A - A * Y.map (starRingEnd ℂ)) = 0 := by
      rw [smul_sub, ← h2, neg_smul]; abel
    rcases smul_eq_zero.mp this with h | h
    · exact absurd h Complex.I_ne_zero
    · exact h
  have h4 : Yᵀ * A = 0 := by
    have : (2 : ℂ) • (Yᵀ * A) = 0 := by
      rw [two_smul]
      calc Yᵀ * A + Yᵀ * A = (Yᵀ * A + A * Y.map (starRingEnd ℂ)) + (Yᵀ * A - A * Y.map (starRingEnd ℂ)) := by abel
        _ = 0 := by rw [h1, h3, add_zero]
    rcases smul_eq_zero.mp this with h | h
    · norm_num at h
    · exact h
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have h5 : Yᵀ = 0 := by
    calc Yᵀ = Yᵀ * A * A⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv A hu, Matrix.mul_one]
      _ = 0 := by rw [h4, Matrix.zero_mul]
  simpa using congrArg Matrix.transpose h5

/- English proof (translation)
Use `set u := skewSub A`. Set `f : (u × u) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ` to `u.subtype ∘ₗ LinearMap.fst ℝ u u + (Complex.I • LinearMap.id) ∘ₗ u.subtype ∘ₗ LinearMap.snd ℝ u u`. Establish `hf : Function.Injective f`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨a, b⟩ hab`.

Establish `hab' : (a : Matrix (Fin r) (Fin r) ℂ) + Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) = 0`. Simplify `hab` using `[f]`. Establish `hIb : Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) ∈ u`. Establish `: Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) = -(a : Matrix (Fin r) (Fin r) ℂ)` using `eq_neg_of_add_eq_zero_right hab'`. Rewrite using `[this]`.

Conclude with `u.neg_mem a.2`. Establish `hb : (b : Matrix (Fin r) (Fin r) ℂ) = 0` using `eq_zero_of_mem_of_I_smul_mem hA b.2 hIb`. Establish `ha : (a : Matrix (Fin r) (Fin r) ℂ) = 0` using `by simpa [hb] using hab'`. Use `ext1`. Conclude with `Subtype.ext ha`.

Conclude with `Subtype.ext hb`. Use `LinearMap.finrank_le_finrank_of_injective hf` as an intermediate fact. Rewrite `this` using `[Module.finrank_prod, Module.finrank_matrix, Complex.finrank_real_complex]`. Simplify using `only [Fintype.card_fin] at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma finrank_skewSub_mul_two_le {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.det ≠ 0) :
    2 * Module.finrank ℝ (skewSub A) ≤ 2 * (r * r) := by
  set u := skewSub A
  let f : (u × u) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ :=
    u.subtype ∘ₗ LinearMap.fst ℝ u u + (Complex.I • LinearMap.id) ∘ₗ u.subtype ∘ₗ LinearMap.snd ℝ u u
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hab' : (a : Matrix (Fin r) (Fin r) ℂ) + Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) = 0 := by
      simpa [f] using hab
    have hIb : Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) ∈ u := by
      have : Complex.I • (b : Matrix (Fin r) (Fin r) ℂ) = -(a : Matrix (Fin r) (Fin r) ℂ) :=
        eq_neg_of_add_eq_zero_right hab'
      rw [this]; exact u.neg_mem a.2
    have hb : (b : Matrix (Fin r) (Fin r) ℂ) = 0 := eq_zero_of_mem_of_I_smul_mem hA b.2 hIb
    have ha : (a : Matrix (Fin r) (Fin r) ℂ) = 0 := by simpa [hb] using hab'
    ext1
    · exact Subtype.ext ha
    · exact Subtype.ext hb
  have := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_prod, Module.finrank_matrix, Complex.finrank_real_complex] at this
  simp only [Fintype.card_fin] at this
  linarith

/- English proof (translation)
Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality. Establish `: Y = 0` using `Subsingleton.elim _ _`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Use `set u := skewSub A`. Use `set su := u ⊓ LinearMap.ker ((Matrix.traceLinearMap (Fin r) ℂ ℂ).restrictScalars ℝ)`. Establish `hYsu : Y ∈ su` using `⟨hY, by simpa using hYt⟩`. Establish `hle : Submodule.span ℝ (Set.range v) ≤ su`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨(hvu i).1, by simpa using (hvu i).2⟩`. Establish `hIu : Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ) ∈ u`. Rewrite using `[mem_skewSub]`. Establish `hc : (Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ)).map (starRingEnd ℂ) = (-Complex.I) • (1 : Matrix (Fin r) (Fin r) ℂ)`.

Apply the tactic sequence `ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Rewrite using `[hc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, neg_smul, add_neg_cancel]`. Establish `hIsu : Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ) ∉ su`. Introduce and unpack `⟨-, h⟩`. Establish `h' : Matrix.trace (Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ)) = 0` using `by simpa using h`.

Rewrite `h'` using `[Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]`. Break down `mul_eq_zero.mp h' with h'' | h''` into its components or cases. Conclude with `Complex.I_ne_zero h''`. Conclude with `absurd (by exact_mod_cast h'' : r = 0) hr.ne'`. Establish `hlt : su < u` using `lt_of_le_of_ne inf_le_left (fun h => hIsu (h ▸ hIu))`.

Establish `h1` using `Submodule.finrank_lt_finrank_of_lt hlt`. Establish `h2 : 2 * Module.finrank ℝ u ≤ 2 * (r * r)` using `finrank_skewSub_mul_two_le hA`. Establish `hspan` using `finrank_span_eq_card hv`. Rewrite `hspan` using `[Fintype.card_fin]`. Establish `heq : Submodule.span ℝ (Set.range v) = su`.

Apply `Submodule.eq_of_le_of_finrank_le hle` to reduce the goal to its premises. Rewrite using `[hspan, sq]`. Express the relevant statement in the definitionally equal form `Module.finrank ℝ su ≤ r * r - 1`. Generalize the expression as in `r * r = n at h2 ⊢`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[heq]`. Conclude with `hYsu`.
-/
theorem mem_span_of_linearIndependent {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (hA : A.det ≠ 0)
    (v : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ) (hv : LinearIndependent ℝ v)
    (hvu : ∀ i, (v i)ᵀ * A + A * (v i).map (starRingEnd ℂ) = 0 ∧ (v i).trace = 0)
    (Y : Matrix (Fin r) (Fin r) ℂ) (hY : Yᵀ * A + A * Y.map (starRingEnd ℂ) = 0)
    (hYt : Y.trace = 0) : Y ∈ Submodule.span ℝ (Set.range v) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have : Y = 0 := Subsingleton.elim _ _
    rw [this]; exact Submodule.zero_mem _
  set u := skewSub A
  set su := u ⊓ LinearMap.ker ((Matrix.traceLinearMap (Fin r) ℂ ℂ).restrictScalars ℝ)
  have hYsu : Y ∈ su := ⟨hY, by simpa using hYt⟩
  have hle : Submodule.span ℝ (Set.range v) ≤ su := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(hvu i).1, by simpa using (hvu i).2⟩
  have hIu : Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ) ∈ u := by
    rw [mem_skewSub]
    have hc : (Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ)).map (starRingEnd ℂ)
        = (-Complex.I) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
      ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [hc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, neg_smul, add_neg_cancel]
  have hIsu : Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ) ∉ su := by
    rintro ⟨-, h⟩
    have h' : Matrix.trace (Complex.I • (1 : Matrix (Fin r) (Fin r) ℂ)) = 0 := by simpa using h
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at h'
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact Complex.I_ne_zero h''
    · exact absurd (by exact_mod_cast h'' : r = 0) hr.ne'
  have hlt : su < u := lt_of_le_of_ne inf_le_left (fun h => hIsu (h ▸ hIu))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : 2 * Module.finrank ℝ u ≤ 2 * (r * r) := finrank_skewSub_mul_two_le hA
  have hspan := finrank_span_eq_card hv
  rw [Fintype.card_fin] at hspan
  have heq : Submodule.span ℝ (Set.range v) = su := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hspan, sq]
    change Module.finrank ℝ su ≤ r * r - 1
    generalize r * r = n at h2 ⊢
    omega
  rw [heq]; exact hYsu

end GlobalTheory.TracelessSkewSpan
