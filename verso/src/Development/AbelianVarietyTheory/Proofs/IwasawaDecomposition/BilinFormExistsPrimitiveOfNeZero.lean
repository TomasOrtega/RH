import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkValEqZeroOrOne
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab⟩ : ∃ a b, σ a b ≠ 0 := by`. Assume the negation of the conclusion as `h`. Apply `hσ` to reduce the goal to its premises. Use extensionality with `a b`. Assume the negation of the conclusion as `h'`.

Conclude with `h ⟨a, b, by simpa using h'⟩`. Establish `hbound : ∀ k : ℕ, (∃ β' : LinearMap.BilinForm ℤ X, (k : ℤ) • β' = σ) → k ≤ (σ a b).natAbs`. Introduce and unpack `k ⟨β', hβ'⟩`. Establish `h1 : σ a b = (k : ℤ) * β' a b`. Rewrite using `[← hβ']`.

Simplify using the standard rewrite rules. Establish `h2 : k ∣ (σ a b).natAbs` using `Int.natCast_dvd.mp ⟨β' a b, h1⟩`. Conclude with `Nat.le_of_dvd (Int.natAbs_pos.mpr hab) h2`. Set `P : ℕ → Prop` to `fun k => ∃ β' : LinearMap.BilinForm ℤ X, (k : ℤ) • β' = σ`. Establish `hP1 : P 1` using `⟨σ, by simp⟩`.

Establish `h1le : 1 ≤ (σ a b).natAbs` using `hbound 1 hP1`. Establish `hg : P (Nat.findGreatest P (σ a b).natAbs)` using `Nat.findGreatest_spec h1le hP1`. Establish `hg1 : 1 ≤ Nat.findGreatest P (σ a b).natAbs` using `Nat.le_findGreatest h1le hP1`. Establish `hmax : ∀ k, P k → k ≤ Nat.findGreatest P (σ a b).natAbs` using `fun k hk => Nat.le_findGreatest (hbound k hk) hk`. Generalize the expression as in `Nat.findGreatest P (σ a b).natAbs = g at hg hg1 hmax`.

Take `⟨β₀, hβ₀⟩` from `hg`. Use `⟨g, β₀, hg1, hβ₀, ?_⟩` and prove the remaining obligations. Introduce `k β' hk`. Establish `hgk : P (g * k)` using `⟨β', by rw [Nat.cast_mul, mul_smul, hk, hβ₀]⟩`. Establish `hle` using `hmax _ hgk`.

Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Apply `hσ` to reduce the goal to its premises. Rewrite using `[← hβ₀, ← hk]`. Simplify using the standard rewrite rules.

Establish `hk1 : k ≤ 1`. Establish `: g * k ≤ g * 1` using `by simpa using hle`. Conclude with `Nat.le_of_mul_le_mul_left this hg1`. Use linear arithmetic over natural numbers and integers.
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
