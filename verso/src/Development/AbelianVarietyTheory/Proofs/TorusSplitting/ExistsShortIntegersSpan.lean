import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.FD in

/- English proof (translation)
Introduce `E _ _ _`. Set `Λ : Submodule (𝓞 E) (Fin 1 → E)` to `Submodule.span (𝓞 E) {fun _ => 1}`. Establish `hΛ : ∀ x, x ∈ Λ ↔ IsIntegral ℤ (x 0)`. Introduce `x`. Rewrite using `[Submodule.mem_span_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Establish `: (a • (fun _ => 1 : Fin 1 → E)) 0 = (a : E)`. Simplify using `[Algebra.smul_def]`. Rewrite using `[this]`.

Conclude with `a.isIntegral_coe`. Introduce `h`. Use `⟨⟨x 0, h⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Rewrite using `[Subsingleton.elim k 0]`.

Conclude with `mul_one (x 0)`. Establish `hh : ∀ x y : Fin 1 → E, herm 1 x y = x 0 * cc (y 0)`. Introduce `x y`. Simplify using `[herm]`. Establish `hc : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (cc x)` using `fun x hx => hx.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom`.

Take `⟨v, hv, -, hsp, hle⟩` from `exists_short_vectors Λ (Submodule.fg_span_singleton _) (fun x hx y hy => by`. Rewrite using `[hh]`. Conclude with `((hΛ x).1 hx).mul (hc _ ((hΛ y).1 hy)))`. Use the proof step `(fun x hx => by`. Use `hx (fun _ => 1) (Submodule.mem_span_singleton_self _)` as an intermediate fact.

Rewrite `this` using `[hh]`. Rewrite using `[hΛ]`. Simplify `this)` using `[cc]`. Use `⟨_, fun j => ⟨v j 0, (hΛ _).1 (hv j)⟩, fun j σ => ?_, fun α => ?_⟩` and prove the remaining obligations. Establish `h` using `hle j σ`.

Establish `he : 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * ((1 : ℕ) : ℝ) ^ 2 * rdE E = omStar (E` using `E) := by`. Simplify using `only [omStar, Nat.cast_one, one_pow, mul_one]`. Both sides reduce to the same expression. Establish `h0 : 0 ≤ omStar (E` using `E) := by`. Unfold `omStar PT.rd`.

Check the signs of the components of the expression. Rewrite `h` using `[he, Fin.sum_univ_one]`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).1 h`. Establish `h : (fun _ => (α : E) : Fin 1 → E) ∈ Submodule.span ℚ (Set.range v)` using `hsp ▸ Submodule.mem_top`. Establish `h2` using `Submodule.mem_map_of_mem (f := LinearMap.proj (R := ℚ) (φ := fun _ : Fin 1 => E) 0) h`.

Rewrite `h2` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `h2`.
-/
theorem exists_short_integers_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ (n : ℕ) (ω : Fin n → 𝓞 E),
      (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ omStar (E := E)) ∧
        ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)) := by
  intro E _ _ _
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have hΛ : ∀ x, x ∈ Λ ↔ IsIntegral ℤ (x 0) := by
    intro x
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      have : (a • (fun _ => 1 : Fin 1 → E)) 0 = (a : E) := by
        simp [Algebra.smul_def]
      rw [this]
      exact a.isIntegral_coe
    · intro h
      refine ⟨⟨x 0, h⟩, ?_⟩
      funext k
      rw [Subsingleton.elim k 0]
      exact mul_one (x 0)
  have hh : ∀ x y : Fin 1 → E, herm 1 x y = x 0 * cc (y 0) := by
    intro x y
    simp [herm]
  have hc : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (cc x) := fun x hx =>
    hx.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
  obtain ⟨v, hv, -, hsp, hle⟩ := exists_short_vectors Λ (Submodule.fg_span_singleton _)
    (fun x hx y hy => by
      rw [hh]
      exact ((hΛ x).1 hx).mul (hc _ ((hΛ y).1 hy)))
    (fun x hx => by
      have := hx (fun _ => 1) (Submodule.mem_span_singleton_self _)
      rw [hh] at this
      rw [hΛ]
      simpa [cc] using this)
  refine ⟨_, fun j => ⟨v j 0, (hΛ _).1 (hv j)⟩, fun j σ => ?_, fun α => ?_⟩
  · have h := hle j σ
    have he : 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * ((1 : ℕ) : ℝ) ^ 2 * rdE E = omStar (E := E) := by
      simp only [omStar, Nat.cast_one, one_pow, mul_one]
      rfl
    have h0 : 0 ≤ omStar (E := E) := by
      unfold omStar PT.rd
      positivity
    rw [he, Fin.sum_univ_one] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).1 h
  · have h : (fun _ => (α : E) : Fin 1 → E) ∈ Submodule.span ℚ (Set.range v) :=
      hsp ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.proj (R := ℚ) (φ := fun _ : Fin 1 => E) 0) h
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2

end GlobalTheory
