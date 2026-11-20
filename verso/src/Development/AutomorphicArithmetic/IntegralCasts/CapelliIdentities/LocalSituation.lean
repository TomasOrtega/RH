import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

/- English proof (translation)
Introduce `E _ _ _ r X w`. Establish `hw : w ∈ Submodule.span E (X.Λ : Set (Fin r → E))`. Rewrite using `[X.Λ_span]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact X.Λ.zero_mem⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`.

Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `X.Λ.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `X.Λ.smul_mem b hax`.

Rewrite using `[mul_smul]`. Conclude with `X.Λ.smul_mem a hby`. Consider the case `smul t x _ hx`. Take `⟨a, ha, hax⟩` from `hx`. Take `⟨p, q, hq, rfl⟩` from `IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) t`.

Establish `hq0 : q ≠ 0` using `nonZeroDivisors.ne_zero hq`. Establish `hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0`. Simplify using `using hq0`. Use `⟨a * q, mul_ne_zero ha hq0, ?_⟩` and prove the remaining obligations. Establish `key : (a * q) • ((algebraMap (NumberField.RingOfIntegers E) E p / algebraMap (NumberField.RingOfIntegers E) E q) • x) = p • (a • x)`.

Use extensionality with `i`. Simplify using `only [Pi.smul_apply]`. Simplify using `only [Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key]`.

Conclude with `X.Λ.smul_mem p hax`.
-/
theorem UpperTheory.Reformulated.B.LocalSituation.exists_smul_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ}
      (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (w : Fin r → E),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • w ∈ X.Λ := by
  intro E _ _ _ r X w
  have hw : w ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
    rw [X.Λ_span]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact X.Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine X.Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact X.Λ.smul_mem b hax
    · rw [mul_smul]; exact X.Λ.smul_mem a hby
  | smul t x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) t
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      simpa using hq0
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have key : (a * q) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • x) = p • (a • x) := by
      ext i
      simp only [Pi.smul_apply]
      simp only [Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
      field_simp
    rw [key]
    exact X.Λ.smul_mem p hax
