import Mathlib

noncomputable def UpperTheory.Reformulated.B.DYhc9.IsLat :
    {E : Type} → [inst : Field E] → {N : ℕ} → Submodule (NumberField.RingOfIntegers E) (Fin N → E) → Prop :=
    fun {E : Type} [Field E] {N : ℕ} (Λ : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) ↦
      Λ.FG ∧ Submodule.span E (↑Λ : Set (Fin N → E)) = ⊤

/- English proof (translation)
Establish `halg : IsAlgebraic ℤ a`. Establish `: Algebra.IsAlgebraic ℤ E` using `(IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).mpr inferInstance`. Conclude with `Algebra.IsAlgebraic.isAlgebraic a`. Take `⟨r, hr, hint⟩` from `halg.exists_integral_multiple`. Establish `hint' : IsIntegral ℤ ((r : E) * a)` using `by simpa [zsmul_eq_mul] using hint`.

Use `⟨r.natAbs, Int.natAbs_ne_zero.mpr hr, ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq r with h | h` into its components or cases. Establish `: ((r.natAbs : E)) = (r : E)` using `by conv_rhs => rw [h]`. Simplify using the standard rewrite rules. Rewrite using `[this]` and apply the resulting hypothesis.

Establish `: ((r.natAbs : E)) = -(r : E)` using `by conv_rhs => rw [h]`. Simplify using the standard rewrite rules. Rewrite using `[this, neg_mul]`. Conclude with `hint'.neg`.
-/
private theorem UpperTheory.Reformulated.B.DYhc9.exists_denom {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  have halg : IsAlgebraic ℤ a := by
    have : Algebra.IsAlgebraic ℤ E :=
      (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).mpr inferInstance
    exact Algebra.IsAlgebraic.isAlgebraic a
  obtain ⟨r, hr, hint⟩ := halg.exists_integral_multiple
  have hint' : IsIntegral ℤ ((r : E) * a) := by simpa [zsmul_eq_mul] using hint
  refine ⟨r.natAbs, Int.natAbs_ne_zero.mpr hr, ?_⟩
  rcases Int.natAbs_eq r with h | h
  · have : ((r.natAbs : E)) = (r : E) := by
      conv_rhs => rw [h]
      simp
    rwa [this]
  · have : ((r.natAbs : E)) = -(r : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]
    exact hint'.neg

/- English proof (translation)
Introduce `E _ _ N Λ h x`. Establish `hx : x ∈ Submodule.span E (Λ : Set (Fin N → E))`. Rewrite using `[h.2]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨m, hm, hmy⟩` from `hy`. Take `⟨n, hn, hnz⟩` from `hz`.

Use `⟨m * n, mul_ne_zero hm hn, ?_⟩` and prove the remaining obligations. Establish `key : ((m * n : ℕ) : E) • (y + z) = n • ((m : E) • y) + m • ((n : E) • z)`. Use extensionality with `i`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key]`. Conclude with `Λ.add_mem (nsmul_mem hmy n) (nsmul_mem hnz m)`. Consider the case `smul a y _ hy`. Take `⟨m, hm, hmy⟩` from `hy`. Take `⟨d, hd, hint⟩` from `UpperTheory.Reformulated.B.DYhc9.exists_denom a`.

Use `⟨d * m, mul_ne_zero hd hm, ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩ : ∃ b : NumberField.RingOfIntegers E, algebraMap (NumberField.RingOfIntegers E) E b = (d : E) * a` from `⟨_, IsIntegralClosure.algebraMap_mk' _ _ hint⟩`. Establish `key : ((d * m : ℕ) : E) • (a • y) = b • ((m : E) • y)`. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[Algebra.smul_def, hb]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `Λ.smul_mem _ hmy`.
-/
theorem UpperTheory.Reformulated.B.DYhc9.main :
    ∀ {E : Type} [inst : Field E] [NumberField E] {N : ℕ} {Λ : Submodule (NumberField.RingOfIntegers E) (Fin N → E)},
      UpperTheory.Reformulated.B.DYhc9.IsLat Λ → ∀ (x : Fin N → E), ∃ (m : ℕ), m ≠ (0 : ℕ) ∧ (↑m : E) • x ∈ Λ := by
  intro E _ _ N Λ h x
  have hx : x ∈ Submodule.span E (Λ : Set (Fin N → E)) := by
    rw [h.2]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hmy⟩ := hy
    obtain ⟨n, hn, hnz⟩ := hz
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have key : ((m * n : ℕ) : E) • (y + z) = n • ((m : E) • y) + m • ((n : E) • z) := by
      ext i
      simp
      ring
    rw [key]
    exact Λ.add_mem (nsmul_mem hmy n) (nsmul_mem hnz m)
  | smul a y _ hy =>
    obtain ⟨m, hm, hmy⟩ := hy
    obtain ⟨d, hd, hint⟩ := UpperTheory.Reformulated.B.DYhc9.exists_denom a
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    obtain ⟨b, hb⟩ : ∃ b : NumberField.RingOfIntegers E,
        algebraMap (NumberField.RingOfIntegers E) E b = (d : E) * a :=
      ⟨_, IsIntegralClosure.algebraMap_mk' _ _ hint⟩
    have key : ((d * m : ℕ) : E) • (a • y) = b • ((m : E) • y) := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Algebra.smul_def, hb]
      push_cast
      ring
    rw [key]
    exact Λ.smul_mem _ hmy
