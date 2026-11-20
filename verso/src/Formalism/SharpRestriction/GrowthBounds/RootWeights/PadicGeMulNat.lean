import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
import Formalism.GrowthSums.LemmaATwoFactList

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def mah (f : ℕ → ℚ) (j : ℕ) : ℚ := (fwdDiff 1)^[j] f 0

def DecLe (p : ℕ) (θ s : ℝ) (K : ℕ) (f : ℕ → ℚ) : Prop := ∀ j ≤ K, PadicGe p (mah f j) (θ * j + s)

def Dec (p : ℕ) (θ s : ℝ) (f : ℕ → ℚ) : Prop := ∀ j, PadicGe p (mah f j) (θ * j + s)

def HdU (p : ℕ) : Prop := ∀ t rho : ℕ, rho < p ^ (t + 1) → ∃ a : ℕ → ℤ,
  (∀ n : ℕ, dUnit (p ^ (t + 1)) n rho = ∑ l ∈ range (rho + 1), (a l : ℚ) * (n.choose l : ℚ)) ∧
  ∀ l, (p : ℤ) ^ l ∣ a l

def HDec (p : ℕ) : Prop := ∀ u : UnitFn, u.rho < p ^ (u.t + 1) → Dec p (1 / 4) 0 (unitFn p u)

def HUnit (p : ℕ) : Prop := ∀ u : UnitFn, u.rho < p ^ (u.t + 1) → ∀ m : ℕ,
  unitFn p u m ≠ 0 ∧ padicValRat p (unitFn p u m) = 0

def HMul (p : ℕ) : Prop := ∀ (θ s s' : ℝ) (f g : ℕ → ℚ), 0 ≤ θ → Dec p θ s f → Dec p θ s' g →
  Dec p θ (s + s') (fun n => f n * g n)

/- English proof (translation)
Break down `hx with hx | hx` into its components or cases. Substitute `hx` using the available equality. Simplify using `using hy`. Break down `hy with hy | hy` into its components or cases. Substitute `hy` using the available equality.

Rewrite using `[add_zero]`. Conclude with `Or.inr hx`. Distinguish the cases in `hxy : x + y = 0`. Conclude with `Or.inl hxy`. Use `right`.

Establish `hm` using `padicValRat.min_le_padicValRat_add (p := p) hxy`. Establish `hm' : ((min (padicValRat p x) (padicValRat p y) : ℤ) : ℝ) ≤ (padicValRat p (x + y) : ℝ)`. Conclude with `hm` after adjusting the coercions. Rewrite `hm'` using `[Int.cast_min]`. Conclude with `le_trans (le_min hx hy) hm'`.
-/
theorem padicGe_add {p : ℕ} [Fact p.Prime] {x y : ℚ} {r : ℝ} (hx : PadicGe p x r) (hy : PadicGe p y r) :
    PadicGe p (x + y) r := by
  rcases hx with hx | hx
  · subst hx; simpa using hy
  rcases hy with hy | hy
  · subst hy; rw [add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  have hm := padicValRat.min_le_padicValRat_add (p := p) hxy
  have hm' : ((min (padicValRat p x) (padicValRat p y) : ℤ) : ℝ) ≤ (padicValRat p (x + y) : ℝ) := by
    exact_mod_cast hm
  rw [Int.cast_min] at hm'
  exact le_trans (le_min hx hy) hm'

/- English proof (translation)
Break down `hx with hx | hx` into its components or cases. Use `left`. Simplify using `[hx]`. Break down `hy with hy | hy` into its components or cases. Use `left`.

Simplify using `[hy]`. Distinguish the cases in `h0 : x * y = 0`. Conclude with `Or.inl h0`. Use `right`. Establish `hx0 : x ≠ 0` using `left_ne_zero_of_mul h0`.

Establish `hy0 : y ≠ 0` using `right_ne_zero_of_mul h0`. Rewrite using `[padicValRat.mul hx0 hy0]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem padicGe_mul {p : ℕ} [Fact p.Prime] {x y : ℚ} {r s : ℝ} (hx : PadicGe p x r) (hy : PadicGe p y s) :
    PadicGe p (x * y) (r + s) := by
  rcases hx with hx | hx
  · left; simp [hx]
  rcases hy with hy | hy
  · left; simp [hy]
  by_cases h0 : x * y = 0
  · exact Or.inl h0
  right
  have hx0 : x ≠ 0 := left_ne_zero_of_mul h0
  have hy0 : y ≠ 0 := right_ne_zero_of_mul h0
  rw [padicValRat.mul hx0 hy0]
  push_cast
  linarith

/- English proof (translation)
Break down `hx with hx | hx` into its components or cases. Conclude with `Or.inl hx`. Conclude with `Or.inr (le_trans h hx)`.
-/
theorem padicGe_mono {p : ℕ} {x : ℚ} {r s : ℝ} (hx : PadicGe p x r) (h : s ≤ r) : PadicGe p x s := by
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr (le_trans h hx)

/- English proof (translation)
Break down `hx with hx | hx` into its components or cases. Use `left`. Simplify using `[hx]`. Use `right`. Rewrite using `[padicValRat.neg]`.

Conclude with `hx`.
-/
theorem padicGe_neg {p : ℕ} {x : ℚ} {r : ℝ} (hx : PadicGe p x r) : PadicGe p (-x) r := by
  rcases hx with hx | hx
  · left; simp [hx]
  · right; rw [padicValRat.neg]; exact hx

/- English proof (translation)
Distinguish the cases in `hk : (k : ℚ) = 0`. Conclude with `Or.inl hk`. Use `right`. Rewrite using `[padicValRat.of_int]`. Conclude with `(Nat.cast_nonneg _ : (0 : ℤ) ≤ (padicValInt p k : ℤ))` after adjusting the coercions.
-/
theorem padicGe_int {p : ℕ} [Fact p.Prime] (k : ℤ) : PadicGe p (k : ℚ) 0 := by
  by_cases hk : (k : ℚ) = 0
  · exact Or.inl hk
  right
  rw [padicValRat.of_int]
  exact_mod_cast (Nat.cast_nonneg _ : (0 : ℤ) ≤ (padicValInt p k : ℤ))

/- English proof (translation)
Establish `h` using `padicGe_mul hx (padicGe_int (p := p) (k : ℤ))`. Simplify using `using h`.
-/
theorem padicGe_mul_nat {p : ℕ} [Fact p.Prime] {x : ℚ} {r : ℝ} (hx : PadicGe p x r) (k : ℕ) :
    PadicGe p (x * (k : ℚ)) r := by
  have h := padicGe_mul hx (padicGe_int (p := p) (k : ℤ))
  simpa using h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact Or.inl (by simp)`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `padicGe_add (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))`.
-/
theorem padicGe_sum {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ) {r : ℝ}
    (h : ∀ i ∈ s, PadicGe p (f i) r) : PadicGe p (∑ i ∈ s, f i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact padicGe_add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end Formalism.MainNotions.G.GLWeightTheory
