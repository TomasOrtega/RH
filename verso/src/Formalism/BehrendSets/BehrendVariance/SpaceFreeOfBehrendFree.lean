import Formalism.BehrendSets.StatementE
import Mathlib
import Formalism.BehrendSets.BehrendVariance.MulAbsSubLt

open Finset Real

noncomputable section

namespace Formalism.BehrendSets.E3

/- English proof (translation)
Establish `hsm : a • h = b • h`. Establish `: t + a • h = t + b • h` using `by rw [← ea, ← eb]`. Conclude with `add_left_cancel this`. Establish `hz : (a - b) • h = 0` using `by rw [sub_zsmul, hsm]; abel`. Establish `hd : ((addOrderOf h : ℕ) : ℤ) ∣ (a - b)` using `addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz`.

Establish `hlt : |a - b| < ((addOrderOf h : ℕ) : ℤ)`. Establish `: (Lw : ℤ) < ((addOrderOf h : ℕ) : ℤ)` using `by exact_mod_cast hord`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd hlt)`.
-/
lemma idx_eq {n Lw : ℕ} {h u t : ZMod n} (hord : Lw < addOrderOf h) {y : ℕ} {a b : ℤ}
    (hab : |a - b| ≤ (Lw : ℤ)) (ea : ((y : ℕ) : ZMod n) + u = t + a • h)
    (eb : ((y : ℕ) : ZMod n) + u = t + b • h) : a = b := by
  have hsm : a • h = b • h := by
    have : t + a • h = t + b • h := by rw [← ea, ← eb]
    exact add_left_cancel this
  have hz : (a - b) • h = 0 := by rw [sub_zsmul, hsm]; abel
  have hd : ((addOrderOf h : ℕ) : ℤ) ∣ (a - b) := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
  have hlt : |a - b| < ((addOrderOf h : ℕ) : ℤ) := by
    have : (Lw : ℤ) < ((addOrderOf h : ℕ) : ℤ) := by exact_mod_cast hord
    linarith
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd hlt)

/- English proof (translation)
Take `⟨y₁, hy₁, e₁⟩` from `Thick.mem_thick.mp m₁`. Take `⟨y₂, hy₂, e₂⟩` from `Thick.mem_thick.mp m₂`. Take `⟨y₃, hy₃, e₃⟩` from `Thick.mem_thick.mp m₃`. Use `set D : ℤ := (i₃ - i₁) * ((y₂ : ℤ) - y₁) - (i₂ - i₁) * ((y₃ : ℤ) - y₁) with hDdef`. Establish `hZ : ((D : ℤ) : ZMod n) = 0`.

Rewrite using `[hDdef]`. Use `push_cast`. Establish `e₁'` using `e₁`. Establish `e₂'` using `e₂`. Establish `e₃'` using `e₃`.

Rewrite `e₁'`, `e₂'`, `e₃'` using `[zsmul_eq_mul]`. Take the linear combination `((i₂ : ZMod n) - i₃) * e₁' + ((i₃ : ZMod n) - i₁) * e₂' - ((i₂ : ZMod n) - i₁) * e₃'`. Establish `hdvd : (n : ℤ) ∣ D` using `(ZMod.intCast_zmod_eq_zero_iff_dvd D n).mp hZ`. Establish `bd : ∀ y ∈ S, (4 * (Lw : ℤ)) * (y : ℤ) < (n : ℤ)`. Introduce `y hy`.

Use `hS y hy` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hL : (0 : ℤ) ≤ 4 * (Lw : ℤ)` using `by positivity`. Establish `d₂ : 4 * (Lw : ℤ) * |(y₂ : ℤ) - y₁| < n` using `Thick.mul_abs_sub_lt (by positivity) (by positivity) hL (bd y₂ hy₂) (bd y₁ hy₁)`. Establish `d₃ : 4 * (Lw : ℤ) * |(y₃ : ℤ) - y₁| < n` using `Thick.mul_abs_sub_lt (by positivity) (by positivity) hL (bd y₃ hy₃) (bd y₁ hy₁)`.

Apply the tactic sequence `have ha : |i₂ - i₁| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith`. Apply the tactic sequence `have hb : |i₃ - i₁| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith`. Establish `habsD : |D| ≤ |i₃ - i₁| * |(y₂ : ℤ) - y₁| + |i₂ - i₁| * |(y₃ : ℤ) - y₁|`. Rewrite using `[hDdef, ← abs_mul, ← abs_mul]`. Conclude with `abs_sub _ _`.

Establish `k₁ : |i₃ - i₁| * |(y₂ : ℤ) - y₁| ≤ (Lw : ℤ) * |(y₂ : ℤ) - y₁|` using `mul_le_mul_of_nonneg_right hb (abs_nonneg _)`. Establish `k₂ : |i₂ - i₁| * |(y₃ : ℤ) - y₁| ≤ (Lw : ℤ) * |(y₃ : ℤ) - y₁|` using `mul_le_mul_of_nonneg_right ha (abs_nonneg _)`. Establish `hDlt : |D| < (n : ℤ)`. Establish `q₁ : 4 * ((Lw : ℤ) * |(y₂ : ℤ) - y₁|) = 4 * (Lw : ℤ) * |(y₂ : ℤ) - y₁|` using `by ring`. Establish `q₂ : 4 * ((Lw : ℤ) * |(y₃ : ℤ) - y₁|) = 4 * (Lw : ℤ) * |(y₃ : ℤ) - y₁|` using `by ring`.

Establish `: (0 : ℤ) ≤ |D|` using `abs_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hD0 : D = 0` using `Int.eq_zero_of_abs_lt_dvd hdvd hDlt`. Distinguish the cases in `c12 : y₁ = y₂`. Substitute `c12` using the available equality.

Use `idx_eq hord (by rw [abs_sub_comm]; exact ha) e₁ e₂` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `c13 : y₁ = y₃`. Substitute `c13` using the available equality. Use `idx_eq hord (by rw [abs_sub_comm]; exact hb) e₁ e₃` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `c23 : y₂ = y₃`. Substitute `c23` using the available equality. Apply the tactic sequence `have h32 : |i₃ - i₂| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith`. Use `idx_eq hord (by rw [abs_sub_comm]; exact h32) e₂ e₃` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hF (i₂ - i₁) (i₃ - i₁) (by linarith) (by linarith) hw y₁ hy₁ y₂ hy₂ y₃ hy₃ c12 c13 c23 (sub_eq_zero.mp hD0)`.
-/
lemma core {n Lw : ℕ} [NeZero n] {S : Finset ℕ} (hS : ∀ s ∈ S, 4 * Lw * s < n)
    (hF : SpaceFreePos Lw S) {h u t : ZMod n} (hord : Lw < addOrderOf h) {i₁ i₂ i₃ : ℤ}
    (h12 : i₁ < i₂) (h23 : i₂ < i₃) (hw : i₃ - i₁ ≤ (Lw : ℤ))
    (m₁ : t + i₁ • h ∈ thick n S u) (m₂ : t + i₂ • h ∈ thick n S u)
    (m₃ : t + i₃ • h ∈ thick n S u) : False := by
  obtain ⟨y₁, hy₁, e₁⟩ := Thick.mem_thick.mp m₁
  obtain ⟨y₂, hy₂, e₂⟩ := Thick.mem_thick.mp m₂
  obtain ⟨y₃, hy₃, e₃⟩ := Thick.mem_thick.mp m₃
  set D : ℤ := (i₃ - i₁) * ((y₂ : ℤ) - y₁) - (i₂ - i₁) * ((y₃ : ℤ) - y₁) with hDdef
  have hZ : ((D : ℤ) : ZMod n) = 0 := by
    rw [hDdef]
    push_cast
    have e₁' := e₁
    have e₂' := e₂
    have e₃' := e₃
    rw [zsmul_eq_mul] at e₁' e₂' e₃'
    linear_combination ((i₂ : ZMod n) - i₃) * e₁' + ((i₃ : ZMod n) - i₁) * e₂'
      - ((i₂ : ZMod n) - i₁) * e₃'
  have hdvd : (n : ℤ) ∣ D := (ZMod.intCast_zmod_eq_zero_iff_dvd D n).mp hZ
  have bd : ∀ y ∈ S, (4 * (Lw : ℤ)) * (y : ℤ) < (n : ℤ) := by
    intro y hy
    have := hS y hy
    exact_mod_cast this
  have hL : (0 : ℤ) ≤ 4 * (Lw : ℤ) := by positivity
  have d₂ : 4 * (Lw : ℤ) * |(y₂ : ℤ) - y₁| < n :=
    Thick.mul_abs_sub_lt (by positivity) (by positivity) hL (bd y₂ hy₂) (bd y₁ hy₁)
  have d₃ : 4 * (Lw : ℤ) * |(y₃ : ℤ) - y₁| < n :=
    Thick.mul_abs_sub_lt (by positivity) (by positivity) hL (bd y₃ hy₃) (bd y₁ hy₁)
  have ha : |i₂ - i₁| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith
  have hb : |i₃ - i₁| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith
  have habsD : |D| ≤ |i₃ - i₁| * |(y₂ : ℤ) - y₁| + |i₂ - i₁| * |(y₃ : ℤ) - y₁| := by
    rw [hDdef, ← abs_mul, ← abs_mul]
    exact abs_sub _ _
  have k₁ : |i₃ - i₁| * |(y₂ : ℤ) - y₁| ≤ (Lw : ℤ) * |(y₂ : ℤ) - y₁| :=
    mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have k₂ : |i₂ - i₁| * |(y₃ : ℤ) - y₁| ≤ (Lw : ℤ) * |(y₃ : ℤ) - y₁| :=
    mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  have hDlt : |D| < (n : ℤ) := by
    have q₁ : 4 * ((Lw : ℤ) * |(y₂ : ℤ) - y₁|) = 4 * (Lw : ℤ) * |(y₂ : ℤ) - y₁| := by ring
    have q₂ : 4 * ((Lw : ℤ) * |(y₃ : ℤ) - y₁|) = 4 * (Lw : ℤ) * |(y₃ : ℤ) - y₁| := by ring
    have : (0 : ℤ) ≤ |D| := abs_nonneg _
    linarith
  have hD0 : D = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hDlt
  by_cases c12 : y₁ = y₂
  · subst c12
    have := idx_eq hord (by rw [abs_sub_comm]; exact ha) e₁ e₂
    linarith
  by_cases c13 : y₁ = y₃
  · subst c13
    have := idx_eq hord (by rw [abs_sub_comm]; exact hb) e₁ e₃
    linarith
  by_cases c23 : y₂ = y₃
  · subst c23
    have h32 : |i₃ - i₂| ≤ (Lw : ℤ) := by rw [abs_le]; constructor <;> linarith
    have := idx_eq hord (by rw [abs_sub_comm]; exact h32) e₂ e₃
    linarith
  exact hF (i₂ - i₁) (i₃ - i₁) (by linarith) (by linarith) hw y₁ hy₁ y₂ hy₂ y₃ hy₃ c12 c13 c23
    (sub_eq_zero.mp hD0)

end Formalism.BehrendSets.E3

namespace Formalism.BehrendSets

end Formalism.BehrendSets
