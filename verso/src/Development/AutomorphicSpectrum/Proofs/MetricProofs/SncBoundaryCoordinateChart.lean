import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

/- English proof (translation)
Introduce `e X _ A L s nb m W hs hsnc x`. Take `⟨ψ, hψ, hx, hsub, σ, -, -, u, -, hu, hfac⟩` from `hsnc x`. Use `⟨ψ, hψ, hx, Finset.univ.filter (fun i => ∃ k, σ k = some i ∧ m k ≠ 0), ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hglue` using `hs.2 x y y ⟨hsub hy, L.mem_U y⟩`.

Establish `hzero : s y y = 0 ↔ s x y = 0`. Establish `e1 : Real.exp (-L.φ x y) ≠ 0` using `(Real.exp_pos _).ne'`. Establish `e2 : Real.exp (-L.φ y y) ≠ 0` using `(Real.exp_pos _).ne'`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Rewrite `hglue` using `[h, norm_zero, zero_mul]`. Conclude with `norm_eq_zero.mp ((mul_eq_zero.mp hglue).resolve_right e1)`. Introduce `h`. Rewrite `hglue` using `[h, norm_zero, zero_mul]`. Conclude with `norm_eq_zero.mp ((mul_eq_zero.mp hglue.symm).resolve_right e2)`.

Establish `hmem : y ∈ bdry s ↔ s y y = 0` using `Iff.rfl`. Rewrite using `[hmem, hzero, hfac y hy, mul_eq_zero, or_iff_right (hu y hy), Finset.prod_eq_zero_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, -, hk⟩`. Consider the cases of `hσ : σ k with`.

Consider the case `none => simp [hσ] at hk`. Consider the case `some i`. Simplify using `only [hσ] at hk`. Establish `hm : m k ≠ 0`. Introduce `h`.

Rewrite `hk` using `[h, pow_zero]`. Conclude with `one_ne_zero hk`. Conclude with `⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, k, hσ, hm⟩, pow_eq_zero_iff hm |>.mp hk⟩`. Introduce and unpack `⟨i, hi, h0⟩`. Take `⟨k, hk, hm⟩` from `(Finset.mem_filter.mp hi).2`.

Use `⟨k, Finset.mem_univ k, ?_⟩` and prove the remaining obligations. Simplify using `only [hk]`. Rewrite using `[h0, zero_pow hm]`.
-/
theorem bdry_snc_chart :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
      (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X),
      IsSection A L s → IsSNC A L s m W → ∀ x,
        ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
          ∃ S : Finset (Fin e), ∀ y ∈ ψ.source, (y ∈ bdry s ↔ ∃ i ∈ S, ψ y i = 0) := by
  classical
  intro e X _ A L s nb m W hs hsnc x
  obtain ⟨ψ, hψ, hx, hsub, σ, -, -, u, -, hu, hfac⟩ := hsnc x
  refine ⟨ψ, hψ, hx, Finset.univ.filter (fun i => ∃ k, σ k = some i ∧ m k ≠ 0), ?_⟩
  intro y hy
  have hglue := hs.2 x y y ⟨hsub hy, L.mem_U y⟩
  have hzero : s y y = 0 ↔ s x y = 0 := by
    have e1 : Real.exp (-L.φ x y) ≠ 0 := (Real.exp_pos _).ne'
    have e2 : Real.exp (-L.φ y y) ≠ 0 := (Real.exp_pos _).ne'
    constructor
    · intro h
      rw [h, norm_zero, zero_mul] at hglue
      exact norm_eq_zero.mp ((mul_eq_zero.mp hglue).resolve_right e1)
    · intro h
      rw [h, norm_zero, zero_mul] at hglue
      exact norm_eq_zero.mp ((mul_eq_zero.mp hglue.symm).resolve_right e2)
  have hmem : y ∈ bdry s ↔ s y y = 0 := Iff.rfl
  rw [hmem, hzero, hfac y hy, mul_eq_zero, or_iff_right (hu y hy), Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    cases hσ : σ k with
    | none => simp [hσ] at hk
    | some i =>
      simp only [hσ] at hk
      have hm : m k ≠ 0 := by
        intro h
        rw [h, pow_zero] at hk
        exact one_ne_zero hk
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, k, hσ, hm⟩, pow_eq_zero_iff hm |>.mp hk⟩
  · rintro ⟨i, hi, h0⟩
    obtain ⟨k, hk, hm⟩ := (Finset.mem_filter.mp hi).2
    refine ⟨k, Finset.mem_univ k, ?_⟩
    simp only [hk]
    rw [h0, zero_pow hm]

end GlobalTheory.CompanionTheory.Metric
