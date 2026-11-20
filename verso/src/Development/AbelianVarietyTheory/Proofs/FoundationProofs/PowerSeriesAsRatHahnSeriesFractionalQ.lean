import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

/- English proof (translation)
Introduce `Ω _ N hN`. Establish `hN' : (0 : ℚ) < N` using `by exact_mod_cast hN`. Set `f : ℕ →+ ℚ` to `(AddMonoidHom.mulRight ((N : ℚ)⁻¹)).comp (Nat.castAddMonoidHom ℚ)`. Establish `hf : ∀ k : ℕ, f k = (k : ℚ) / N` using `fun k => by`. Simplify using `[f, div_eq_mul_inv]`.

Establish `hfle : ∀ g g' : ℕ, f g ≤ f g' ↔ g ≤ g'` using `fun g g' => by`. Rewrite using `[hf, hf, div_le_div_iff_of_pos_right hN', Nat.cast_le]`. Establish `hfi : Function.Injective f` using `fun g g' h => le_antisymm ((hfle g g').1 h.le) ((hfle g' g).1 h.ge)`. Use `⟨(HahnSeries.embDomainRingHom f hfi hfle).comp (HahnSeries.toPowerSeries (R := Ω)).symm.toRingHom, ?_, ?_⟩` and prove the remaining obligations. Introduce `p k`.

Rewrite using `[← hf]`. Simplify using `only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]`. Rewrite using `[HahnSeries.embDomain_mk_coeff]`. Both sides reduce to the same expression. Introduce `p r hr`.

Simplify using `only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]`. Apply `HahnSeries.embDomain_notin_image_support` to reduce the goal to its premises. Introduce and unpack `⟨k, -, hk⟩`. Conclude with `hr k (by rw [← hf]; exact hk.symm)`.
-/
theorem powerSeries_to_hahnSeries_rat :
    ∀ (Ω : Type) [Field Ω] (N : ℕ), 0 < N → ∃ Φ : PowerSeries Ω →+* HahnSeries ℚ Ω, (∀ (p : PowerSeries Ω) (k : ℕ), (Φ p).coeff ((k : ℚ) / N) = PowerSeries.coeff k p) ∧ ∀ (p : PowerSeries Ω) (r : ℚ), (∀ k : ℕ, r ≠ (k : ℚ) / N) → (Φ p).coeff r = 0 := by
  intro Ω _ N hN
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  let f : ℕ →+ ℚ := (AddMonoidHom.mulRight ((N : ℚ)⁻¹)).comp (Nat.castAddMonoidHom ℚ)
  have hf : ∀ k : ℕ, f k = (k : ℚ) / N := fun k => by
    simp [f, div_eq_mul_inv]
  have hfle : ∀ g g' : ℕ, f g ≤ f g' ↔ g ≤ g' := fun g g' => by
    rw [hf, hf, div_le_div_iff_of_pos_right hN', Nat.cast_le]
  have hfi : Function.Injective f := fun g g' h =>
    le_antisymm ((hfle g g').1 h.le) ((hfle g' g).1 h.ge)
  refine ⟨(HahnSeries.embDomainRingHom f hfi hfle).comp
    (HahnSeries.toPowerSeries (R := Ω)).symm.toRingHom, ?_, ?_⟩
  · intro p k
    rw [← hf]
    simp only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
    rw [HahnSeries.embDomain_mk_coeff]
    rfl
  · intro p r hr
    simp only [RingHom.comp_apply, HahnSeries.embDomainRingHom_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨k, -, hk⟩
    exact hr k (by rw [← hf]; exact hk.symm)

end GlobalTheory
