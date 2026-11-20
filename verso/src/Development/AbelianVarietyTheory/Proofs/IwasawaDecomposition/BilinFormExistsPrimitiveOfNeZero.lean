import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory

/- English proof (translation)
Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Replace the chosen expression with an arbitrary variable. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem bilinForm_exists_primitive_of_ne_zero (X : Type) [AddCommGroup X]
    (σ : LinearMap.BilinForm ℤ X) (hσ : σ ≠ 0) :
    ∃ (g : ℕ) (β₀ : LinearMap.BilinForm ℤ X), 0 < g ∧ (g : ℤ) • β₀ = σ ∧
      ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β₀ → k = 1 := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b, σ a b ≠ 0 := by
    by_contra h
    apply hσ
    ext a b
    by_contra h'
    exact h ⟨a, b, by simpa using h'⟩
  have hbound : ∀ k : ℕ, (∃ β' : LinearMap.BilinForm ℤ X, (k : ℤ) • β' = σ) →
      k ≤ (σ a b).natAbs := by
    rintro k ⟨β', hβ'⟩
    have h1 : σ a b = (k : ℤ) * β' a b := by
      rw [← hβ']
      simp
    have h2 : k ∣ (σ a b).natAbs := Int.natCast_dvd.mp ⟨β' a b, h1⟩
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hab) h2
  let P : ℕ → Prop := fun k => ∃ β' : LinearMap.BilinForm ℤ X, (k : ℤ) • β' = σ
  have hP1 : P 1 := ⟨σ, by simp⟩
  have h1le : 1 ≤ (σ a b).natAbs := hbound 1 hP1
  have hg : P (Nat.findGreatest P (σ a b).natAbs) := Nat.findGreatest_spec h1le hP1
  have hg1 : 1 ≤ Nat.findGreatest P (σ a b).natAbs := Nat.le_findGreatest h1le hP1
  have hmax : ∀ k, P k → k ≤ Nat.findGreatest P (σ a b).natAbs :=
    fun k hk => Nat.le_findGreatest (hbound k hk) hk
  generalize Nat.findGreatest P (σ a b).natAbs = g at hg hg1 hmax
  obtain ⟨β₀, hβ₀⟩ := hg
  refine ⟨g, β₀, hg1, hβ₀, ?_⟩
  intro k β' hk
  have hgk : P (g * k) := ⟨β', by rw [Nat.cast_mul, mul_smul, hk, hβ₀]⟩
  have hle := hmax _ hgk
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hσ
    rw [← hβ₀, ← hk]
    simp
  have hk1 : k ≤ 1 := by
    have : g * k ≤ g * 1 := by simpa using hle
    exact Nat.le_of_mul_le_mul_left this hg1
  omega

end GlobalTheory
