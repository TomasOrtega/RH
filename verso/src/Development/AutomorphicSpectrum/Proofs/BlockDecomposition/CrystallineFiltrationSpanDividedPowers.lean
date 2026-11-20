import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

/- English proof (translation)
The claim follows from `Subtype.ext (by simp [PAlg.dxi0, dpw])`.
-/
theorem divided_power_xi_zero : A.dxi0 0 = 1 :=
  Subtype.ext (by simp [PAlg.dxi0, dpw])

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `hi` using `A.isUnit_natCast (Nat.factorial_ne_zero i)`. Establish `hj` using `A.isUnit_natCast (Nat.factorial_ne_zero j)`. Establish `hij` using `A.isUnit_natCast (Nat.factorial_ne_zero (i + j))`. Express the relevant statement in the definitionally equal form `dpw i A.xi * dpw j A.xi = (((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi`.

Simplify using `only [dpw]`. Apply `hij.mul_left_cancel` to reduce the goal to its premises. Establish `hc : (((i + j).factorial : ℕ) : WL l A.A) = (((i + j).choose i : ℕ) : WL l A.A) * ((i.factorial : ℕ) : WL l A.A) * ((j.factorial : ℕ) : WL l A.A)`. Use `Nat.add_choose_mul_factorial_mul_factorial i j` as an intermediate fact. Rewrite `this` using `[← Nat.choose_symm_add]`.

Rewrite using `[← Nat.cast_mul, ← Nat.cast_mul, this]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = (((i + j).choose i : ℕ) : WL l A.A) * (algebraMap _ (WL l A.A) A.xi ^ (i + j)) := by`.

Rewrite using `[Ring.mul_inverse_cancel _ hi, Ring.mul_inverse_cancel _ hj, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Rewrite using `[mul_left_comm, ← mul_assoc (((i + j).factorial : ℕ) : WL l A.A), Ring.mul_inverse_cancel _ hij, one_mul]`.
-/
theorem divided_power_xi_mul (i j : ℕ) :
    A.dxi0 i * A.dxi0 j = (((i + j).choose i : ℕ) : A.Acr0) * A.dxi0 (i + j) := by
  apply Subtype.ext
  have hi := A.isUnit_natCast (Nat.factorial_ne_zero i)
  have hj := A.isUnit_natCast (Nat.factorial_ne_zero j)
  have hij := A.isUnit_natCast (Nat.factorial_ne_zero (i + j))
  change dpw i A.xi * dpw j A.xi = (((i + j).choose i : ℕ) : WL l A.A) * dpw (i + j) A.xi
  simp only [dpw]
  apply hij.mul_left_cancel
  have hc : (((i + j).factorial : ℕ) : WL l A.A) =
      (((i + j).choose i : ℕ) : WL l A.A) * ((i.factorial : ℕ) : WL l A.A) * ((j.factorial : ℕ) : WL l A.A) := by
    have := Nat.add_choose_mul_factorial_mul_factorial i j
    rw [← Nat.choose_symm_add] at this
    rw [← Nat.cast_mul, ← Nat.cast_mul, this]
  calc _ = (((i + j).choose i : ℕ) : WL l A.A) * (((i.factorial : ℕ) : WL l A.A) * Ring.inverse ((i.factorial : ℕ) : WL l A.A))
        * (((j.factorial : ℕ) : WL l A.A) * Ring.inverse ((j.factorial : ℕ) : WL l A.A))
        * (algebraMap _ (WL l A.A) A.xi ^ i * algebraMap _ (WL l A.A) A.xi ^ j) := by
          rw [hc]; ring
    _ = (((i + j).choose i : ℕ) : WL l A.A) * (algebraMap _ (WL l A.A) A.xi ^ (i + j)) := by
          rw [Ring.mul_inverse_cancel _ hi, Ring.mul_inverse_cancel _ hj, pow_add]; ring
    _ = _ := by
          rw [mul_left_comm, ← mul_assoc (((i + j).factorial : ℕ) : WL l A.A), Ring.mul_inverse_cancel _ hij, one_mul]

def spanFrom (r : ℕ) : Submodule A.W A.Acr0 :=
  Submodule.span A.W {z : A.Acr0 | ∃ k, r ≤ k ∧ z = A.dxi0 k}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨k, h, rfl⟩`.
-/
theorem divided_power_xi_mem_span_from {r k : ℕ} (h : r ≤ k) : A.dxi0 k ∈ spanFrom A r :=
  Submodule.subset_span ⟨k, h, rfl⟩

/- English proof (translation)
Rewrite using `[← nsmul_eq_mul]`. Conclude with `(spanFrom A r).toAddSubmonoid.nsmul_mem hz n`.
-/
theorem natCast_mul_mem (r : ℕ) (n : ℕ) {z : A.Acr0} (hz : z ∈ spanFrom A r) :
    (n : A.Acr0) * z ∈ spanFrom A r := by
  rw [← nsmul_eq_mul]
  exact (spanFrom A r).toAddSubmonoid.nsmul_mem hz n

/- English proof (translation)
Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, -, rfl⟩` from `hx`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨j, hj, rfl⟩` from `hy`. Rewrite using `[divided_power_xi_mul]`. Conclude with `natCast_mul_mem A r _ (divided_power_xi_mem_span_from A (by omega))`. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy => rw [mul_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c hx`. Consider the case `zero => rw [zero_mul]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem mul_mem_spanFrom (r : ℕ) {a b : A.Acr0} (ha : a ∈ spanFrom A 0) (hb : b ∈ spanFrom A r) :
    a * b ∈ spanFrom A r := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, -, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      rw [divided_power_xi_mul]
      exact natCast_mul_mem A r _ (divided_power_xi_mem_span_from A (by omega))
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Take `⟨y, hy⟩` from `z`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨k, rfl⟩` from `hy`. Conclude with `divided_power_xi_mem_span_from A (Nat.zero_le k)`.

Consider the case `algebraMap x`. Establish `h` using `Submodule.smul_mem (spanFrom A 0) x (divided_power_xi_mem_span_from A (le_refl 0))`. Rewrite `h` using `[divided_power_xi_zero]`. Use `h using 1` and compare the differences between its conclusion and the goal. Conclude with `Subtype.ext (by simp [Algebra.smul_def])`.

Consider the case `add x y hx' hy' hx hy => exact add_mem hx hy`. Consider the case `mul x y hx' hy' hx hy => exact mul_mem_spanFrom A 0 hx hy`.
-/
theorem mem_spanFrom_zero (z : A.Acr0) : z ∈ spanFrom A 0 := by
  obtain ⟨y, hy⟩ := z
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact divided_power_xi_mem_span_from A (Nat.zero_le k)
  | algebraMap x =>
    have h := Submodule.smul_mem (spanFrom A 0) x (divided_power_xi_mem_span_from A (le_refl 0))
    rw [divided_power_xi_zero] at h
    convert h using 1
    exact Subtype.ext (by simp [Algebra.smul_def])
  | add x y hx' hy' hx hy => exact add_mem hx hy
  | mul x y hx' hy' hx hy => exact mul_mem_spanFrom A 0 hx hy

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span hx`. Consider the case `zero => exact zero_mem _`.

Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul c x _ hx => exact mul_mem_spanFrom A r (mem_spanFrom_zero A c) hx`. Introduce `h`. Proceed by induction on `h using Submodule.span_induction with`. Consider the case `mem x hx => exact Ideal.subset_span hx`.

Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `smul c x _ hx`. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ hx`.
-/
theorem mem_crystalline_filtration_iff_span {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) (z : A.Acr0) :
    z ∈ A.Fil0 r ↔ z ∈ Submodule.span A.W {z : A.Acr0 | ∃ k, r ≤ k ∧ z = A.dxi0 k} := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx => exact mul_mem_spanFrom A r (mem_spanFrom_zero A c) hx
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ hx

end GlobalTheory.CompanionTheory.PerfFil
