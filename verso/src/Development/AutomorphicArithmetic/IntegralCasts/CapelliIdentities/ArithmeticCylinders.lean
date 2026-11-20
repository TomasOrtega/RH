import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem UpperTheory.Reformulated.B.ArithmeticCylinders.eigen_pow_eq_one :
    ∀ {L : Type} [inst : Field L] {d : Type} [inst_1 : Fintype d] [inst_2 : DecidableEq d]
    (M : Matrix d d L) (n : ℕ), M ^ n = (1 : Matrix d d L) → ∀ (μ : L), M.charpoly.IsRoot μ → μ ^ n = (1 : L) := by
  intro L _ d _ _ M n hM μ hμ
  have h1 : μ ∈ spectrum L M := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hμ
  have h2 : μ ^ n ∈ spectrum L (M ^ n) := spectrum.pow_mem_pow M n h1
  rw [hM, spectrum.mem_iff] at h2
  by_contra hne
  apply h2
  have hu : IsUnit (μ ^ n - 1) := (sub_ne_zero.mpr hne).isUnit
  have h3 := hu.map (algebraMap L (Matrix d d L))
  rwa [map_sub, map_one] at h3
